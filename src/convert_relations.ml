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
(*          Brian Campbell, University of Edinburgh                       *)
(*          Shaked Flur, University of Cambridge                          *)
(*          Thomas Bauereiss, University of Cambridge                     *)
(*          Stephen Kell, University of Cambridge                         *)
(*          Thomas Williams                                               *)
(*          Lars Hupel                                                    *)
(*          Basile Clement                                                *)
(*                                                                        *)
(*  The Lem sources are copyright 2010-2018                               *)
(*  by the authors above and Institut National de Recherche en            *)
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

(* Converting a relation *)

open Typed_ast
open Types
open Util
open Typed_ast_syntax

(* FIXME *)
let raise_error l m f x = raise (Reporting_basic.err_type_pp l m f x)

let r = Ulib.Text.of_latin1
let newline = Some [Ast.Nl]
let space = Some [Ast.Ws(r" ")]

module Converter(C : Exp_context) = struct

module C = Exps_in_context(C)
open C

module Nmap = Typed_ast.Nfmap
module Nset = Nmap.S

(** [sep_no_skips l] converts the list [l] into a Seplist with empty
    separator. *)
let sep_no_skips (l : 'a list) : 'a lskips_seplist =
  Seplist.from_list_default None l


(** [sep_newline l] converts the list [l] into a Seplist with newline
    separator *)
let sep_newline l = Seplist.from_list_default newline l

(* TODO: Move to util. *)
(** Binary type to represent a choice. *)
type ('a,'b) choice = Left of 'a | Right of 'b

(** [map_partition f l] maps [f] over [l] and partitions the result
    between the [Left] and [Right] values. *)
let map_partition (f : 'a -> ('b, 'c) choice) (l : 'a list) : 'b list * 'c list =
  List.fold_right (fun x (ls,rs) ->
    match f x with
      | Left l -> (l::ls,rs)
      | Right r -> (ls,r::rs)
  ) l ([],[])

(******************************************************************************)
(* Auxiliary functions acting on the AST                                      *)
(******************************************************************************)

(* Locations                                                                  *)

(** [loc_trans s l] is a simple wrapper around [Ast.Trans] that
    annotates [l] with the translation information [s]. *)
let loc_trans (s : string) (l : Ast.l) : Ast.l =
  Ast.Trans (true, s, Some l)

(* Types                                                                      *)

(** [remove_option ty] removes the maybe constructor from type
    [maybe t], and fails otherwise. *)
(* TODO: This actually removes any type constructor.  It should
   probably not be done at all, but this requires some serious
   refactoring. *)
let remove_option (ty : Types.t) : Types.t =
  match ty.t with
  | Types.Tapp([ty], _) -> ty
  | _ -> failwith "???"

(** [mk_tup_unit_typ tys] converts the list of types [tys] into a
    single tuple type. *)
let mk_tup_unit_typ : t list -> t = function
  | [] -> unit_ty
  | [t] -> t
  | l -> {t=Ttup(l)}

(* Constants                                                                  *)

(** [const_descr] is a helper function for the construction of a
    [const_descr] with (hopefully) sane defaults. *)
let const_descr
    ~binding ?(tparams=[]) ?(class_=[])
    ?(no_class=Target.Targetmap.empty)
    ?(ranges=[]) ~type_ ?(relation_info=None)
    ~env_tag ?(targets=Target.Targetset.empty)
    ~l ?(target_rename=Target.Targetmap.empty)
    ?(target_rep=Target.Targetmap.empty)
    ?(target_ascii_rep=Target.Targetmap.empty)
    ?(compile_message=Target.Targetmap.empty)
    ?(termination_setting=Target.Targetmap.empty)
    ()
  : const_descr =
  { const_binding = binding ;
    const_tparams = tparams ;
    const_class = class_ ;
    const_no_class = no_class ;
    const_ranges = ranges ;
    const_type = type_ ;
    relation_info = relation_info ;
    env_tag = env_tag ;
    const_targets = targets ;
    spec_l = l ;
    target_rename = target_rename ;
    target_rep = target_rep ;
    target_ascii_rep = target_ascii_rep ;
    compile_message = compile_message ;
    termination_setting = termination_setting }

(** [and_const_ref env] represent the Lem constant [&&] in environment
    [env] *)
let and_const_ref (env : env) : const_descr_ref =
  fst (get_const env "conjunction")

(** [eq_const_ref env] represent the Lem equality function in
    environment [env]. *)
let eq_const_ref (env : env) : const_descr_ref =
  fst (get_const env "equality")

(** [cdr_instantiate env l c_ref inst] transforms the constant [c_ref]
    into an expression by instantiating it with the types in
    [inst]. *)
let cdr_instantiate
    (env : env) (l : Ast.l) (c_ref : const_descr_ref)
    (inst : Types.t list)
  : exp
  =
  let id = { id_path = Id_none None;
             id_locn = l;
             descr = c_ref;
             instantiation = inst } in
  let c_d = c_env_lookup l env.c_env c_ref in
  let t = Types.type_subst 
    (Types.TNfmap.from_list2 c_d.const_tparams id.instantiation) 
    c_d.const_type in
  C.mk_const l id (Some t)

(** [mk_tup_unit_exp l es] converts the list of expressions [es] into
    a single tuple expression. *)
let mk_tup_unit_exp l : exp list -> exp = function
  | [] -> mk_lit l (mk_lunit l None (Some unit_ty)) (Some unit_ty)
  | [e] -> e
  | es -> mk_tup l None (sep_no_skips es) None None

(** [mk_const_app env l label inst args] constructs the application of
    [label] to arguments [args] with type instantiation [inst]. *)
let mk_const_app
    (env : env) (l : Ast.l) (label : string)
    (inst : Types.t list) (args : exp list)
  : exp =
  let c = mk_const_exp env l label inst in
  List.fold_left (fun u v -> mk_app l u v None) c args

let mk_none env l ty = mk_const_app env l "maybe_nothing" [ty] []
let mk_some env l e = mk_const_app env l "maybe_just" [exp_to_typ e] [e]

(* Patterns                                                                   *)

(** [mk_tup_unit_pat l ps] converts the list of patterns [ps] into a
    single pattern on tuples. *)
let mk_tup_unit_pat l : pat list -> pat= function
  | [] -> mk_plit l (mk_lunit l None (Some unit_ty)) None
  | [p] -> p
  | ps -> mk_ptup l None (sep_no_skips ps) None None

(** [mk_pconst_pat env l label inst args] constructs the pattern
    matching values of shape [label (args)] where the type variables in
    the type of [label] have been instantiated with the types in
    [inst]. *)
let mk_pconst_pat (env : env) (l : Ast.l) (label : string)
    (inst : t list) (args : pat list) : pat =
  let (c, c_d) = get_const_id env l label inst in
  let t = Types.type_subst
    (Types.TNfmap.from_list2 c_d.const_tparams c.instantiation)
    c_d.const_type in
  let (_, t) = Types.strip_fn_type (Some env.t_env) t in
  mk_pconst l c args (Some t)

(* Relation information                                                       *)

(** [c_env_lookup_rel_info l c_env c_ref] extracts the relation
    information for [c_ref] in [c_env] with a default value. *)
let c_env_lookup_rel_info
    (l : Ast.l) (c_env : c_env) (c_ref : const_descr_ref)
  : rel_info =
  let c_d = c_env_lookup l c_env c_ref in
  match c_d.relation_info with
  | Some(x) -> x
  | None -> { ri_witness = None ;
              ri_check = None ;
              ri_fns = [] }

(** [c_env_update_rel_info l c_env c_ref ri] updates the relation
    information for [c_ref] in [c_env] with [ri] *)
let c_env_update_rel_info
    (l : Ast.l) (c_env : c_env) (c_ref : const_descr_ref)
    (ri : rel_info)
  : c_env =
  let c_d = c_env_lookup l c_env c_ref in
  c_env_update c_env c_ref { c_d with relation_info = Some(ri) }

type mode_spec =
  (* The input/output specifiers *)
  rel_mode
  (* Should witnesses be generated? *)
  * bool
  (* The monad in which code should be generated *)
  * rel_output_type

(** Describes a rule [rn: forall x1 .. xn, P1 && .. && Pn ==> R t1 .. tn] *)
type ruledescr = {
  (** Name of the rule [rn] *)
  rule_name : Name.t;

  (** Quantified variables [x1 .. xn] *)
  rule_vars : (Name.t * Types.t) list;

  (** Conditions [P1 .. Pn] *)
  rule_conds : exp list;

  (** Arguments for the conclusion [t1 .. tn] *)
  rule_args : exp list;

  (** Source location for the definition *)
  rule_loc : Ast.l;
}

(** Describes a relation *)
type reldescr = {
  (** Name of the relation *)
  rel_name : Name.t;

  (** Reference to the defined constant. *)
  rel_const_ref : const_descr_ref;

  (** Type scheme of the relation. *)
  rel_type : typschm;

  (** Types of the relation's arguments *)
  rel_argtypes : Types.t list;

  (** Name of the witness type if we must generate one. *)
  rel_witness : Name.t option;

  (** Name of the witness checking function if we must generate one. *)
  rel_check : Name.t option;

  (** Name and modes of the functions that should be generated. *)
  rel_indfns : (Name.t * mode_spec) list;

  (** The rules determining this relation. *)
  rel_rules : ruledescr list;

  (** Source location for the indreln block. *)
  rel_loc : Ast.l;
}

type relsdescr = reldescr Nfmap.t

(** Converts the source types "input" and "output" to [Rel_mode_in]
    and [Rel_mode_out] respectively. *)
(* TODO: This should probably be done earlier in the process (at the
   point the check is made to only allow "input" and "output" here *)
let to_in_out (typ : src_t) : rel_io =
  match typ.term with
  | Typ_app({id_path = Id_some i }, []) ->
    begin match Name.to_string (Name.strip_lskip (Ident.get_name i)) with
      | "input" -> Rel_mode_in
      | "output" -> Rel_mode_out
      | s -> raise (Invalid_argument ("to_in_out: "^s))
    end
  | _ -> raise (Invalid_argument "to_in_out")

(** The default output mode if not specified. *)
(* TODO: Out_pure is broken; only Out_list is working. *)
let default_out_mode = Out_pure

(** [src_t_to_mode typ] converts the type with source annotations
    [typ] into a mode specification, i.e. a list of input/output
    specifiers for the arguments, a boolean indicating whether a
    witness should be generated, and a [rel_output_type] specification
    for the monad in which to generate the code. *)
(* TODO: This should probably be done earlier, see [to_in_out]. *)
let rec src_t_to_mode (typ : src_t) : mode_spec =
  match typ.term with
    | Typ_paren(_,t,_)
    | Typ_with_sort(t,_) -> src_t_to_mode t
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

(******************************************************************************)
(* Extracting a relation description                                          *)
(******************************************************************************)

(** Extract the arguments types from a relation. *)
let rec decompose_rel_type (typ : src_t) : Types.t list =
  match typ.term with
    | Typ_fn(u,_,v) -> u.typ::decompose_rel_type v
    | _ -> [] (* The return value is assumed to be bool, we don't check it *)

(** Extract the relation descriptions from a seplist of [indreln_name].
    The extracted relation doesn't have any rule information. *)
let get_relsdescr_from_names
    (l : Ast.l) (names : indreln_name lskips_seplist)
  : relsdescr =
  Seplist.fold_left (fun (RName (_, n, c_ref, _, t, wit, chk, fn, _)) s ->
      let relname = Name.strip_lskip n in
      let witness_name =
        option_map (fun (Indreln_witness (_, _, n, _)) ->
            Name.strip_lskip n) wit in
      let check_name =
        option_map (fun (_, n, _) -> Name.strip_lskip n) chk in
      let (_constraints, typ) = t in
      let argtypes  =
        decompose_rel_type typ in
      let indfns =
        List.map
          (fun (Indreln_fn (n, _, t, _)) ->
             (Name.strip_lskip n, src_t_to_mode t))
          (option_default [] fn) in
      let descr =
        { rel_name = relname ;
          rel_const_ref = c_ref ;
          rel_type = t ;
          rel_argtypes = argtypes ;
          rel_witness = witness_name ;
          rel_check = check_name ;
          rel_indfns = indfns ;
          rel_rules = [] ;
          rel_loc = l
        }
      in
      Nfmap.insert s (relname, descr))
    Nfmap.empty names

(** [add_rules_to_relsdescr env rules descr] adds the rules from
    [rules] to the relation descriptions in [descrs].

    [env] is used to detect conjunctions in the hypotheses.

    For every rule in [rules], its relation must have an associated
    relation description in [descrs], otherwise the function fails.
*)
let add_rules_to_relsdescr
    (env : env) (rules : indreln_rule lskips_seplist)
    (descrs : relsdescr)
  : relsdescr =
  Seplist.fold_left (fun (Rule (n, _, _, vars, _, cond, _, rel, _, args), l) s ->
      let l' = loc_trans "add_rules_to_relsdescr" l in
      let rulecond =
        match cond with
        | Some x -> x
        | None -> mk_tf_exp true in
      let extract_name = function
        | QName n -> n
        | Name_typ (_, n, _, _, _) -> n in
      let typed_vars =
        List.map (fun qv ->
            let v = extract_name qv in
            (Name.strip_lskip v.term, v.typ))
          vars in
      let ruledescr = {
        rule_name = Name.strip_lskip n ;
        rule_vars = typed_vars ;
        rule_conds = dest_and_exps env rulecond ;
        rule_args = args ;
        rule_loc = l'
      } in
      let relname = Name.strip_lskip rel.term in
      match Nfmap.apply s relname with
      | None ->
        failwith "Relation without description"
      | Some rel ->
        Nfmap.insert s
          (relname, { rel with rel_rules = ruledescr :: rel.rel_rules }))
    descrs rules

(** [get_rels env l names rules] combines both
    [add_rules_to_relsdescr] and [get_relsdescr_from_names] to extract
    the full relation description from the relation in [names] with
    rules in [rules]. *)
let get_rels (env : env) (l : Ast.l) (names : indreln_name lskips_seplist)
    (rules: indreln_rule lskips_seplist) : relsdescr =
  add_rules_to_relsdescr env rules
    (get_relsdescr_from_names l names)


(* A small model of the code we will generate later *)
type code =
  (* [IF (e, c)] becomes
       [if e then [[c]] else fail] *)
  | IF of exp * code
  (* [CALL (fn, [e1; ..; en], [p1; ..; pn], c)] becomes
       [bind (fn e1 .. en) (function | (p1, .., pn) -> [[c]] | _ -> fail)] *)
  | CALL of const_descr_ref * exp list * pat list * code
  (* [LET (p, e, c)] becomes
       [match e with | p -> [[c]] | _ -> fail] *)
  | LET of pat * exp * code
  (* [RETURN (e1, ..., en)] becomes
       [return (e1, ..., en)] *)
  | RETURN of exp list

exception No_translation of exp option
let no_translation e = raise (No_translation e)

(** [make_namegen names] returns a name generator that
    - Never generates twice the same name.
    - Never generates a name from the set [names]
*)
let make_namegen (names : Nset.t) : Ast.text -> Name.t =
  let names = ref names in
  let fresh n =
    let n' = Name.fresh n (fun n -> not (Nset.mem n !names)) in
    names := Nset.add n' !names;
    n'
  in
  fresh

(** [extract_exp l env e avoid] creates a new variable [v] (whose name is
    not in [avoid]) and returns

    - A pattern matching on this variable

    - An equation [v = e] asserting that this variable is equal to [e] *)
let extract_exp
    (l : Ast.l) (env : env) (e : exp) (avoid : Nset.t ref)
  : pat * exp =
  let l = loc_trans "extract_exp" l in
  let n =
    Name.fresh (r"pat") (fun n -> not (Nset.mem n !avoid)) in
  let v = Name.add_lskip n in
  let ty = exp_to_typ e in
  let pat =
    mk_pvar_annot l v (t_to_src_t ty) (Some ty) in
  let var =
    mk_var l v ty in
  avoid := Nset.add n !avoid;
  (pat, (mk_eq_exp env var e))

(** [linearize env pats avoid seen] constructs:

    - New patterns from [pats] where duplicate variables have been
    renamed with names not present in [!avoid]. [avoid] is updated to
    contains the generated names.

    - A list of equalities that between the renamed variables and
    their initial names that must be satisfied for the new pattern(s)
    to be equivalent to the old one(s).

    - [seen] is updated with the name of all variables bound by the
      pattern, and contains a set of already-bound names.

    For instance, when called with a pattern [C (x, K (y, x), y)], it
    returns the new pattern [C (x, K (y, x'), y')] and the list of
    equations [[ y = y' ; x = x']]. *)
let linearize
    (env : env) (pats : pat list) (avoid : Nset.t ref)
    (seen : Nset.t ref)
  : pat list * exp list =
  let eqs = ref [] in
  (* Constructs a fresh variable and registers its equalities *)
  let make_fresh (n : Name.lskips_t) (l : Ast.l) (t : Types.t)
    : Name.lskips_t =
    let n' =
      Name.lskip_rename
        (fun v ->
           if not (Nset.mem (Name.from_rope v) !seen) then v
           else Name.(to_rope (fresh v (fun n -> not (Nset.mem n !avoid)))))
        n
    in
    let v = Name.strip_lskip n in
    let v' = Name.strip_lskip n' in
    if v <> v' then
      eqs :=
        (mk_eq_exp env
           (mk_var l (Name.add_lskip v) t)
           (mk_var l (Name.add_lskip v') t))
        :: !eqs;
    avoid := Nset.add v (Nset.add v' !avoid);
    seen := Nset.add v !seen;
    n' in
  let rec linearize_pat (p : pat) : pat =
    let ty = p.typ in
    let l = loc_trans "linearize" p.locn in
    match p.term with
    | P_wild s -> mk_pwild l s ty
    | P_as (s1, p', s2, (n, l'), s3) ->
      mk_pas l s1 (linearize_pat p') s2
        (make_fresh n l ty, l') s3 (Some ty)
    | P_typ (s1, p', s2, t, s3) ->
      mk_ptyp l s1 (linearize_pat p') s2 t s3 (Some ty)
    | P_var n ->
      mk_pvar l (make_fresh n l ty) ty
    | P_const (cdr, pats) ->
      mk_pconst l cdr (List.map linearize_pat pats) (Some ty)
    | P_backend (s1, ident, t, pats) ->
      mk_pbackend l s1 ident t (List.map linearize_pat pats) (Some ty)
    | P_record (s1, fs, s2) ->
      let fs' =
        Seplist.map (fun (cd, s, p) ->
            (cd, s, linearize_pat p)) fs in
      mk_precord l s1 fs' s2 (Some ty)
    | P_vector (s1, ps, s2) ->
      mk_pvector l s1 (Seplist.map linearize_pat ps) s2 ty
    | P_vectorC (s1, ps, s2) ->
      mk_pvectorc l s1 (List.map linearize_pat ps) s2 ty
    | P_tup (s1, ps, s2) ->
      mk_ptup l s1 (Seplist.map linearize_pat ps) s2 (Some ty)
    | P_list (s1, ps, s2) ->
      mk_plist l s1 (Seplist.map linearize_pat ps) s2 ty
    | P_paren (s1, p, s2) ->
      mk_pparen l s1 (linearize_pat p) s2 (Some ty)
    | P_cons (p1, s, p2) ->
      mk_pcons l (linearize_pat p1) s
        (linearize_pat p2) (Some ty)
    | P_num_add ((n, l'), s1, s2, i) ->
      mk_pnum_add l (make_fresh n l ty, l') s1 s2 i (Some ty)
    | P_lit lit ->
      mk_plit l lit (Some ty)
    | P_var_annot (n, t) ->
      mk_pvar_annot l (make_fresh n l ty) t (Some ty)
  in
  let pats' = List.map linearize_pat pats in
  (pats', !eqs)

(** [mk_if_code env es c] guards the code [c] with conditions in
    [es] *)
let mk_if_code (env : env) (es : exp list) (c : code) : code=
  if es = [] then c
  else IF (mk_and_exps env es, c)

(** [linearize_code env seen avoid c] transforms the code [c] such
    that any variable appearing several times in [c] (either in patterns
    or expressions) are actually linked to the same variable.

    Effectively, any variable appearing in a pattern except the first time
    it is encountered is replaced by a fresh variable that is checked to
    be equal to the old one.

    The [!seen] set contains the variables that are already bound by a
    pattern in the current scope, and the [!avoid] set contains variable
    names that must not be used for fresh variables (and is expected to be
    a superset of the [!seen] set).

    WARNING: [!seen] actually contains *all* the variables encountered
    by the current search in the current code. This is not a problem
    right now as there is no branching, however. *)
let rec linearize_code
  (env : env) (seen : Nset.t ref)
  (avoid : Nset.t ref) (c : code)
  : code =
  match c with
  | IF (e, c) -> IF (e, linearize_code env seen avoid c)
  | CALL (cd, es, ps, c) ->
    let (ps, eqs) = linearize env ps seen avoid in
    CALL (cd, es, ps,
          mk_if_code env eqs (linearize_code env seen avoid c))
  | LET (p, e, c) ->
    let (p, eqs) = linearize env [p] seen avoid in
    LET (List.hd p, e,
         mk_if_code env eqs (linearize_code env seen avoid c))
  | RETURN es -> RETURN es

(** [dest_list_app_exp e] converts an expression into a couple of an
    applied function and the list of its arguments. It is roughly an
    inverse of [mk_list_app_exp], except that it looks deep into
    parentheses and similar constructs.

    For instance, [f x y z] is transformed into [(f, [x; y; z])]. *)
let dest_list_app_exp (e : exp) : exp * exp list =
  let rec dest_list_app_exp e args = match exp_to_term e with
    | App(e1,e2) -> dest_list_app_exp e1 (e2::args)
    | Paren(_,e,_) | Begin(_,e,_) | Typed(_,e,_,_,_) -> dest_list_app_exp e args
    | Infix(e2, e1, e3) -> dest_list_app_exp e1 (e2::e3::args)
    | _ -> (e,args)
  in
  dest_list_app_exp e []

(** [is_constructor env t c_d] checks whether [c_d] is a constructor
    for type [t] in environment [env]. *)
let is_constructor
    (env : env) (t : Types.t) (c_d : const_descr_ref) : bool
  =
  match type_defs_lookup_typ Ast.Unknown env.t_env t with
  | None -> false
  | Some(td) ->
    List.exists (fun cfd ->
        List.mem c_d cfd.constr_list
      ) td.type_constr

(** [is_list_cons env cons] checks whether [cons] is the list `cons'
    operator (::) in environment [env]. *)
let is_list_cons
    (env : env) (cons : const_descr_ref) : bool
  =
  cons = fst (get_const env "list_cons")

(** [is_list_append env append] checks whether [append] is the list
    `append` operator (++) in environment [env]. *)
let is_list_append
    (env : env) (append : const_descr_ref)
  : bool =
  append = fst (get_const env "list_append")

(** [is_num_add env add] checks whether [add] is the addition operator
    on numbers `Num.+` *)
let is_num_add
    (env : env) (add : const_descr_ref)
  : bool =
  add = fst (get_const env "addition")
(** [exps_to_pats avoid env es] returns a pair [(ps, eqs)], where:

    - [ps] is a list of same length as [es], where each expression in
    [es] have been translated into a pattern ; that is, each pattern
    in [ps] match exactly the expressions of same shape as the
    corresponding expression in [es], if moreover the guards in [eqs]
    are respected.

    - [eqs] is a list of guards for the patterns. When encountering a
    complex expression that can't directly be translated into a
    pattern (such as a function call), [exps_to_pats] creates a fresh
    variable to put in the pattern, and adds the equality between this
    variable and the initial expression in [eqs]. For instance, the
    translation of [[f x :: y]] would be [[x' :: y]] as a pattern, and
    [[x' = f x]] as guarded equality.

    The fresh variables generated avoid the names in [avoid], and are
    added to [avoid] afterwards.

    Note that the patterns may not be linear (yet), and that one must
    call [linearize] at some point after calling [exps_to_pats]. This
    also means that the free variables appearing in the side condition
    may be bound in the pattern - for instance, the translation of
    [f x :: x] would give [x' :: x] as a pattern and [x' = f x] as a
    guard. *)
let exps_to_pats (avoid : Nset.t ref) (env : env) (es : exp list)
  : pat list * exp list =
  let eqs = ref [] in
  let rec exp_to_pat e =
    let loc = loc_trans "exp_to_pat" (exp_to_locn e) in
    let ty = exp_to_typ e in
    let (head, args) = dest_list_app_exp e in
    match exp_to_term head, args with
    (* Cons is treated differently than other constructors in
       patterns. *)
    | Constant cons, [e1;e2] when is_list_cons env cons.descr ->
      let p1 = exp_to_pat e1 in
      let p2 = exp_to_pat e2 in
      mk_pcons loc p1 None p2 (Some ty)
    | Constant cd, [e1;e2] when is_list_append env cd.descr ->
      let p1 = exp_to_pat e1 in
      let p2 = exp_to_pat e2 in
      begin match p1.term, p2.term with
        (* [[x1 ; .. ; xn] ++ [y1 ; .. yn ]] is [x1 ; .. ; xn ; y1 ; .. ; yn] *)
        | P_list (s1, ps, s2), P_list (s1', ps', s2') ->
          mk_plist loc s1
            (Seplist.append s2 ps (Seplist.cons_sep s1' ps'))
            s2' p2.typ
        (* [[x1 ; .. ; xn] ++ l] is [x1 :: .. :: xn :: l] *)
        | P_list (s1, ps, s2), _ ->
          mk_pparen loc s1
            (Seplist.fold_right
               (fun p r ->
                  mk_pcons loc p None r (Some ty))
               p2 ps)
            s2 (Some ty)
        (* [[] ++ l] is [l] *)
        | _, P_list (_, ps, _) when Seplist.length ps = 0 -> p1
        | _ ->
          Reporting.print_debug_exp env "Extracting complex list expression" [e];
          let (p, eq) = extract_exp loc env e avoid in
          eqs := eq :: !eqs;
          p
      end
    | Constant c, args when is_constructor env ty c.descr ->
      let pargs =
        List.fold_right (fun e (pats) ->
            let p = exp_to_pat e in
            (p :: pats)) args ([]) in
      mk_pconst loc c pargs (Some ty)
    | Var v, [] ->
      mk_pvar_annot loc v (t_to_src_t ty) (Some ty)
    | Record(s1, fields, s2), [] ->
      let pfields =
        Seplist.map (fun (cd, s, e, _loc) ->
            (cd, s, exp_to_pat e)) fields in
      mk_precord loc s1 pfields s2 (Some ty)
    | Vector(s1, es, s2), [] ->
      let ps = Seplist.map exp_to_pat es in
      mk_pvector loc s1 ps s2 ty
    | Tup(s1, es, s2), [] ->
      let ps = Seplist.map exp_to_pat es in
      mk_ptup loc s1 ps s2 (Some ty)
    | List(s1, es, s2), [] ->
      let ps = Seplist.map exp_to_pat es in
      mk_plist loc s1 ps s2 ty
    | Lit l, [] ->
      mk_plit loc l (Some ty)
    (* TODO: Sets *)
    | _ ->
      Reporting.print_debug_exp env "Extracting non-pattern expression" [e];
      let (p, eq) = extract_exp loc env e avoid in
      eqs := eq :: !eqs;
      p in
  let ps = List.map exp_to_pat es in
  (ps, !eqs)

(** [exp_to_pat avoid env e] converts expression [e] into a pattern.

    See [exps_to_pats]. *)
let exp_to_pat (avoid : Nset.t ref) (env : env) (e : exp)
  : pat * exp list =
  let (ps, eqs) = exps_to_pats avoid env [e] in
  (List.hd ps, eqs)

(** [pat_to_bound p] returns the variables bound by [p]. *)
let pat_to_bound (p : pat) : Types.t Nmap.t =
  p.rest.pvars

(** [pats_to_bound ps] returns the variables bound by a pattern in
    [ps]. *)
let pats_to_bound (ps : pat list) : Types.t Nmap.t =
  List.fold_left (fun bound p ->
      Nfmap.union p.rest.pvars bound)
    Nfmap.empty ps

module Pat : sig
  type t
  val bound : t list -> Types.t Nmap.t
  val linearize : t list -> t list
  val simplify : t -> t
  val from_exp : env -> exp -> t
  val to_pats : env -> Nset.t ref -> t list -> pat list * exp Nmap.t
end = struct

  type aux =
    | IP_lit of lit
    | IP_list of t list
    | IP_cons of t * t
    | IP_append of t * t
    | IP_tuple of t list
    | IP_vector of t list
    | IP_record of (Types.const_descr_ref Types.id * t) list
    | IP_var of string
    | IP_constant of Types.const_descr_ref Types.id * t list
    | IP_fresh of exp
   and t =
     { loc : Ast.l
     ; typ : Types.t
     ; pat : aux }

  let bound ips =
    let rec bound_ map ip =
      match ip.pat with
      | IP_lit _ | IP_fresh _ -> map
      | IP_list ips
      | IP_tuple ips
      | IP_vector ips
      | IP_constant (_, ips) ->
         List.fold_left bound_ map ips
      | IP_cons (l, r)
      | IP_append (l, r) ->
         bound_ (bound_ map l) r
      | IP_record fields ->
         List.fold_left (fun map (_, ip) -> bound_ map ip) map fields
      | IP_var v ->
         Nmap.insert map (Name.from_string v, ip.typ)
    in
    List.fold_left bound_ Nmap.empty ips

  let linearize (ips : t list) : t list =
    let vars = Hashtbl.create 17 in
    let rec linearize_aux (ip : t) =
      let self = linearize_aux in
      let { loc; typ; pat } = ip in
      match pat with
      | IP_lit _ | IP_fresh _ -> ip
      | IP_list ips ->
         { ip with pat = IP_list (List.map self ips) }
      | IP_cons (l, r) ->
         { ip with pat = IP_cons (self l, self r) }
      | IP_append (l, r) ->
         { ip with pat = IP_append (self l, self r) }
      | IP_tuple ips ->
         { ip with pat = IP_tuple (List.map self ips) }
      | IP_vector ips ->
         { ip with pat = IP_vector (List.map self ips) }
      | IP_record fields ->
         { ip with pat = IP_record
                           (List.map (fun (cd, ip) -> (cd, self ip)) fields) }
      | IP_var s ->
         if Hashtbl.mem vars s then
           let n = Name.add_lskip @@ Name.from_string s in
           { ip with pat = IP_fresh (mk_var loc n typ) }
         else begin
             Hashtbl.add vars s ();
             ip
           end
      | IP_constant (cd, args) ->
         { ip with pat = IP_constant (cd, List.map self args) }
    in List.map linearize_aux ips

  let rec simplify (ip : t) =
    let { loc; typ; pat } = ip in
    match pat with
    | IP_lit _ | IP_fresh _ | IP_var _ -> ip
    | IP_list l ->
       { ip with pat = IP_list (List.map simplify l) }
    | IP_cons (left, right) ->
       let sleft = simplify left in
       let sright = simplify right in
       begin match sright.pat with
             | IP_list ips ->
                { ip with pat = IP_list (sleft :: ips) }
             | _ ->
                { ip with pat = IP_cons (sleft, sright) }
       end
    | IP_append (left, right) ->
       let sleft = simplify left in
       let sright = simplify right in
       begin match sleft.pat, sright.pat with
             | IP_list pl, IP_list pr ->
                { ip with pat = IP_list (pl @ pr) }
             | _, IP_list [] ->
                sleft
             | IP_list pl, _ ->
                List.fold_right
                  (fun hd tl ->
                   { loc = hd.loc; typ = tl.typ; pat = IP_cons (hd, tl) })
                  pl sright
             | _ ->
                { ip with pat = IP_append (sleft, sright) }
       end
    | IP_tuple ips ->
       { ip with pat = IP_tuple (List.map simplify ips) }
    | IP_vector ips ->
       { ip with pat = IP_vector (List.map simplify ips) }
    | IP_record fields ->
       { ip with pat = IP_record
                         (List.map (fun (c, ip) ->
                                    (c, simplify ip))
                                   fields) }
    | IP_constant (cd, args) ->
       { ip with pat = IP_constant (cd, List.map simplify args) }

  let rec from_exp (env : env) (exp : exp) =
    let self = from_exp env in
    let loc = loc_trans "from_exp" (exp_to_locn exp) in
    let typ = exp_to_typ exp in
    let head, args = dest_list_app_exp exp in
    match exp_to_term head, args with
    | Constant nil, [] when is_nil_const_descr_ref nil.descr ->
       { loc; typ; pat = IP_list [] }
    | Constant cons, [e1; e2] when is_list_cons env cons.descr ->
       { loc; typ; pat = IP_cons (self e1, self e2) }
    | Constant cd, [e1; e2] when is_list_append env cd.descr ->
       { loc; typ; pat = IP_append (self e1, self e2) }
    | Constant c, args when is_constructor env typ c.descr ->
       { loc; typ; pat = IP_constant (c, List.map self args) }
    | Var v, [] ->
       { loc; typ; pat = IP_var Name.(to_string @@ strip_lskip v) }
    | Record (_, fields, _), [] ->
       let ip_fields =
         List.map (fun (cd, _, e, _) ->
                   (cd, self e))
         @@ Seplist.to_list fields in
       { loc; typ; pat = IP_record ip_fields }
    | Vector (_, es, _), [] ->
       let ips = List.map self @@ Seplist.to_list es in
       { loc; typ; pat = IP_vector ips }
    | Tup (_, es, _), [] ->
       let ips = List.map self @@ Seplist.to_list es in
       { loc; typ; pat = IP_tuple ips }
    | List (_, es, _), [] ->
       let ips = List.map self @@ Seplist.to_list es in
       { loc; typ; pat = IP_list ips }
    | Lit l, [] ->
       { loc; typ; pat = IP_lit l }
    | _ ->
       { loc; typ; pat = IP_fresh exp }

  let rec to_exp (env : env) (ip : t) =
    let self = to_exp env in
    let { loc; typ; pat } = ip in
    let loc = loc_trans "to_exp" loc in
    match pat with
    | IP_lit l ->
       mk_lit loc l (Some typ)
    | IP_list ips ->
       let es = List.map self ips in
       let es_sep = Seplist.from_list_default space es in
       mk_list loc space es_sep space typ
    | IP_cons (l, r) ->
       let el, er = self l, self r in
       let cons = Typed_ast_syntax.mk_const_exp env loc "list_cons" [exp_to_typ el] in
       mk_list_app_exp loc env.t_env cons [el; er]
    | IP_append (l, r) ->
       let el, er = self l, self r in
       let append = Typed_ast_syntax.mk_const_exp
                      env loc "list_append"
                      [remove_option @@ exp_to_typ el] in
       mk_list_app_exp loc env.t_env append [el; er]
    | IP_tuple ips ->
       let es = List.map self ips in
       let es_sep = Seplist.from_list_default space es in
       mk_tup loc space es_sep space (Some typ)
    | IP_vector ips ->
       let es = List.map self ips in
       let es_sep = Seplist.from_list_default space es in
       mk_vector loc space es_sep space typ
    | IP_record ip_fields ->
       let es_fields =
         List.map (fun (cd, ip) ->
                   (cd, space, self ip, ip.loc))
                  ip_fields in
       let sep_fields = Seplist.from_list_default space es_fields in
       mk_record loc space sep_fields space (Some typ)
    | IP_var s ->
       let n = Name.add_lskip @@  Name.from_string s in
       mk_var loc n typ
    | IP_constant (cd, args) ->
       let es_args = List.map self args in
       let const = mk_const loc cd None in
       mk_list_app_exp loc env.t_env const es_args
    | IP_fresh e -> e

  let to_pats (env : env) (avoid : Nset.t ref) (ips : t list) : pat list * exp Nmap.t =
    let mapping = ref Nmap.empty in
    let rec to_pat ip =
      let { loc; typ; pat } = ip in
      let loc = loc_trans "to_pats" loc in
      match pat with
      | IP_lit l ->
         mk_plit loc l (Some typ)
      | IP_fresh e ->
         let n =
           Name.fresh (r"pat") (fun n -> not (Nset.mem n !avoid)) in
         avoid := Nset.add n !avoid;
         mapping := Nmap.insert !mapping (n, e);
         mk_pvar_annot loc (Name.add_lskip n) (t_to_src_t typ) (Some typ)
      | IP_list ips ->
         let ps = List.map to_pat ips in
         let sep_ps = Seplist.from_list_default space ps in
         mk_plist loc space sep_ps space typ
      | IP_cons (x, xs) ->
        mk_pcons loc (to_pat x) space (to_pat xs) (Some typ)
      | IP_append (p1, p2) ->
         to_pat { ip with pat = IP_fresh (to_exp env ip) }
      | IP_tuple ips ->
         let ps = List.map to_pat ips in
         let sep_ps = Seplist.from_list_default space ps in
         mk_ptup loc space sep_ps space (Some typ)
      | IP_vector ips ->
         let ps = List.map to_pat ips in
         let sep_ps = Seplist.from_list_default space ps in
         mk_pvector loc space sep_ps space typ
      | IP_record fields ->
         let p_fields =
           List.map (fun (cd, ip) ->
                     (cd, space, to_pat ip))
                    fields in
         let sep_fields = Seplist.from_list_default space p_fields in
         mk_precord loc space sep_fields space (Some typ)
      | IP_var s ->
         mk_pvar_annot
           loc
           (Name.add_lskip @@ Name.from_string s)
           (t_to_src_t typ)
           (Some typ)
      | IP_constant (cd, args) ->
         let pargs = List.map to_pat args in
         mk_pconst loc cd pargs (Some typ)
    in
    let pats = List.map to_pat ips in
    (pats, !mapping)

end

(** [extract_patterns env avoid exps mask] converts the expressions from
    [exps] at positions where the corresponding value in [mask] is
    [true] into patterns.

    It also returns the equalities that have been generated to extract
    the non-patternizable expressions (e.g. function calls), see
    [exps_to_pats]. *)
let extract_patterns
      (env : env) (avoid : Nset.t ref) (exps : exp list)
      (mask : bool list)
    : pat list * exp list =
  let wanted =
    map_filter (fun (e, m) -> if m then Some e else None)
               (List.map2 (fun x y -> (x, y)) exps mask) in
  let pats, map =
    Pat.to_pats env avoid @@
      Pat.linearize @@
        List.map (Pat.from_exp env) wanted in
  let eqs =
    Nmap.fold (fun lst n e ->
               let v = mk_var Ast.Unknown (Name.add_lskip n) (exp_to_typ e) in
               mk_eq_exp env v e :: lst)
              [] map in
  pats, eqs

(** [mk_pvar_ty l n t] creates a typed variable pattern, e.g. [(x : int)] *)
let mk_pvar_ty l n t =
  mk_ptyp l space (mk_pvar l n t) None (t_to_src_t t) None None

(* a compilation context takes care of generating real Lem code from
   the monadic mini-language.

   It encapsulate some abstract monadic type constructor [m] in which
   the generated code "lives". *)
module type COMPILATION_CONTEXT = sig
  (* [mk_type t] returns the type [m t] *)
  val mk_type : Types.t -> Types.t

  (* [mk_failure env l t] constructs a value of type [m t] that
     indicates failure (None, empty list, ...)

     It should be read as
       [fail]
     and its type should be understood as
       [type a -> exp (m a)]. *)
  val mk_failure : Typed_ast.env -> Ast.l -> Types.t -> Typed_ast.exp

  (* [mk_return env l e] is a monadic return.

     It should be read as
       [return `e`]
     and its type should be understood as
       [exp a -> exp (m a)]. *)
  val mk_return : Typed_ast.env -> Ast.l -> Types.t -> exp -> exp

  (* [mk_bind env l x pat res] is a monadic bind, returning [res] when
     expression [x] matches the pattern [pat] and indicating a failure
     otherwise.

     It should be read as
       [bind `x` (function | `pat` -> `res` | _ -> fail)]
     and its type should be understood as
       [exp (m a) -> pat a -> exp (m b) -> exp (m b)]. *)
  val mk_bind : env -> Ast.l -> Types.t -> Types.t -> exp -> pat -> exp -> exp

  (* [mk_cond env l cond expr] returns the monadic expression [expr]
     if the boolean expression [cond] is true, and indicates a filure
     otherwise.

     It should be read as
       [if `cond` then `expr` else fail]
     and its type should be understood as
       [exp bool -> exp (m a) -> exp (m a)]. *)
  val mk_cond : Typed_ast.env -> Ast.l -> Types.t -> Typed_ast.exp -> Typed_ast.exp -> Typed_ast.exp

  (* [mk_let env l pat exp res] is a monadic let, returning [res] when
     expression matches the pattern [pat] and indicating a failure
     otherwise.

     It should be read as
       [match `exp`  with | `pat` -> `res` | _ -> fail]
     and its type should be understood as
       [pat a -> exp a -> exp (m b) -> exp (m b)]. *)
  val mk_let : Typed_ast.env -> Ast.l -> Typed_ast.pat -> Typed_ast.exp -> Typed_ast.exp -> Typed_ast.exp

  (* [mk_choice env l ty exp branches] is a branching operation.

     It should be read as
       [match `exp` with `branches` | _ -> fail]
     and its type should be understood as
       [type b -> exp a -> (pat a * exp (m b)) list -> exp (m b)]. *)
  val mk_choice : Typed_ast.env -> Ast.l -> Types.t -> Typed_ast.exp ->
    (Typed_ast.pat * Typed_ast.exp) list -> Typed_ast.exp
end

module type MONAD = sig
  (* `[t] -> `[m t] *)
  val mk_type : Types.t -> Types.t

  (* env -> l -> `[m t] -> `{m t} *)
  val mk_failure : env -> Ast.l -> Types.t -> exp

  (* env -> l -> `[t] -> `{t} -> `{m t} *)
  val mk_return : env -> Ast.l -> Types.t -> exp -> exp

  (* env -> l -> `[m t] -> `{m t} list -> `{m t} *)
  val mk_choose : env -> Ast.l -> Types.t -> exp list -> exp

  (* env -> l -> `[a] -> `[m b] -> `{a} -> `{a -> m b} -> `{m b} *)
  val mk_bind : env -> Ast.l -> Types.t -> Types.t -> exp -> exp -> exp
end

module Monad_list : MONAD = struct
  let mk_type (ty : Types.t) : Types.t =
    list_ty ty

  let mk_return (env : env) (l_org : Ast.l) (ty : Types.t) (e : exp) =
    let l = loc_trans "Monad_list.mk_return" l_org in
    mk_list (loc_trans "mk_return" l) None (sep_no_skips [e]) None
      (mk_type ty)

  let mk_failure env l m_ty =
    mk_list (loc_trans "mk_failure" l) None (sep_no_skips []) None
      m_ty

  let mk_list_concat (env : env) (l : Ast.l) (m_ty : Types.t) (lst : exp) =
    type_eq l "mk_list_concat" (exp_to_typ lst) (list_ty m_ty);
    let l = loc_trans "mk_list_concat" l in
    mk_app l (mk_const_exp env l "list_concat" [remove_option m_ty]) lst
      (Some m_ty)

  let mk_choose (env : env) (l_org : Ast.l) (m_ty : Types.t) (args : exp list) =
    let l = loc_trans "mk_choose [List]" l_org in
    let result =
      mk_list_concat env l m_ty @@
    mk_list l None
      (sep_newline args)
        None (list_ty @@ m_ty) in
    result

  let mk_bind
      (env : env) (l_org : Ast.l) (inty : Types.t) (m_outy : Types.t) (x : exp) (fn : exp) : exp =
    let l = loc_trans "Monad_list.mk_bind" l_org in
    mk_list_concat env l m_outy @@
    mk_list_app_exp l env.t_env
      (mk_const_exp env l "list_map" [inty; m_outy]) [fn; x]
end

module Monad_pure : MONAD = struct
  let mk_type (ty : Types.t) : Types.t = ty

  let mk_return (env : env) (l_org : Ast.l) (ty : Types.t) (e : exp) : exp =
    e

  let mk_failure (env : env) (l_org : Ast.l) (m_ty : Types.t) =
    mk_undefined_exp (loc_trans "Monad_pure.mk_failure" l_org) "Undef" m_ty

  let mk_choose (env : env) (l_org : Ast.l) (m_ty : Types.t) (args : exp list) =
    match args with
    | [] -> mk_failure env l_org m_ty
    | [ arg ] -> arg
    | arg :: _ ->
      Reporting.report_warning env @@
      Reporting.Warn_general
        (true, l_org,
         "You should not use pure mode for branching relations. " ^
         "The generated code will be incomplete.");
      arg

  let mk_bind
    (env : env) (l_org : Ast.l) (inty : Types.t) (m_outy : Types.t) (x : exp) (fn : exp) : exp =
    mk_app l_org fn x (Some m_outy)
end

module Monad_option : MONAD = struct
  let mk_type (ty : Types.t) : Types.t =
    option_ty ty

  let mk_return (env : env) (l_org : Ast.l) (ty : Types.t) (e : exp) : exp =
    mk_const_app env l_org "maybe_just" [ty] [e]

  let mk_failure (env : env) (l_org : Ast.l) (m_ty : Types.t) : exp =
    mk_const_app env l_org "maybe_nothing" [remove_option m_ty] []

  let rec mk_choose (env : env) (l_org : Ast.l) (m_ty : Types.t) (args : exp list) =
    let l = loc_trans "Monad_option.mk_choose" l_org in
    match args with
    | [] -> mk_failure env l_org m_ty
    | [ arg ] -> arg
    | arg :: args' ->
      let ty = remove_option m_ty in
      let x_name = Name.add_lskip @@ Name.from_string "x" in
      mk_case_exp true l arg
        [ mk_pconst_pat env l "maybe_nothing" [ty] [],
          mk_choose env l m_ty args'
        ; mk_pconst_pat env l "maybe_just" [ty] [ mk_pvar l x_name ty ],
          mk_return env l ty @@ mk_var l x_name ty ]
        m_ty

  let mk_bind
    (env : env) (l_org : Ast.l) (inty : Types.t) (m_outy : Types.t) (x : exp) (fn : exp) : exp =
    let l = loc_trans "Monad_option.mk_bind" l_org in
    mk_list_app_exp l env.t_env
      (mk_const_exp env l "maybe_bind" [inty; remove_option @@ m_outy]) [x; fn]
end

(* Monad definition for the "unique" monad, i.e. the option monad with
   the additional requirement that every time a choice must be
   performed, at most one branch returns a meaningful value. *)
module Monad_unique : MONAD = struct
  include Monad_option

  let mk_choose _ = failwith "Not implemented"
end


module Make_Generic_Context(Monad : MONAD) : COMPILATION_CONTEXT = struct
  let mk_type (ty : Types.t) : Types.t =
    Monad.mk_type ty

  let mk_failure (env : env) (l : Ast.l) (m_ty : Types.t) : exp =
    let result = Monad.mk_failure env l m_ty in
    type_eq l "Internal: mk_failure result consistency" (exp_to_typ result) m_ty;
    result

  let mk_return (env : env) (l : Ast.l) (ty : Types.t) (e : exp) : exp =
    type_eq l "Internal: mk_return arguments consistency" (exp_to_typ e) ty;
    let result = Monad.mk_return env l ty e in
    type_eq l "Internal: mk_return result consistency" (exp_to_typ result) (mk_type ty);
    result

  let mk_choose (env : env) (l : Ast.l) (m_ty : Types.t) (args : exp list) : exp =
    List.iter (fun arg ->
        type_eq l "Internal: mk_choose arguments consistency" (exp_to_typ arg) (m_ty))
      args;
    let result = Monad.mk_choose env l m_ty args in
    type_eq l "Internal: mk_choose result consistency" (exp_to_typ result) (m_ty);
    result

  (** [if `cond` then `code` else fail] *)
  let mk_cond (env : env) (l_org : Ast.l) (ty : Types.t) (cond : exp) (code : exp) : exp =
    let l = loc_trans "mk_cond [Generic]" l_org in
    type_eq l "Internal: mk_cond condition consistency" (exp_to_typ cond) bool_ty;
    type_eq l "Internal: mk_cond argument consistency" (exp_to_typ code) (mk_type ty);
    let result = mk_if_exp l cond code (mk_failure env l @@ mk_type ty) in
    type_eq l "Internal: mk_cond result consistency" (exp_to_typ result) (mk_type ty);
    result

  let mk_choice
      (env : env) (l_org : Ast.l) (m_ty : Types.t)
      (input : exp) (pats : (pat * exp) list) : exp =
    let l = loc_trans "mk_choice [Generic]" l_org in
    List.iter
      (fun (p, e) ->
         assert_equal l "Internal: mk_choice arg consistency" env.t_env
           (exp_to_typ e) m_ty;
         assert_equal l "Internal: mk_choice pat consistency" env.t_env
           (annot_to_typ p) (exp_to_typ input))
      pats;
    let case = mk_case_exp false l input pats m_ty in
    assert_equal l "Internal: case consistency" env.t_env
      (exp_to_typ case) m_ty;
    let case_opt =
      Patterns.compile_relation_exp env
        mk_failure mk_choose
        case in
    option_default case case_opt

  let mk_bind
      (env : env) (l_org : Ast.l) (inty : Types.t) (m_outy : Types.t)
      (x : exp) (pat : pat) (res : exp) : exp =
    let l = loc_trans "mk_bind [Generic]" l_org in
    type_eq l "Internal: mk_bind bound check" (exp_to_typ x) (mk_type inty);
    type_eq l "Internal: mk_bind pat check" (annot_to_typ pat) inty;
    type_eq l "Internal: mk_bind output check" (exp_to_typ res) (m_outy);
    let namegen = make_namegen (Nfmap.domain (exp_to_free res)) in
    let var = Name.add_lskip (namegen (r"x")) in
    let body =
      mk_choice env l m_outy (mk_var l var inty) [pat, res] in
    (* fn : inty -> list outy *)
    let fn =
      mk_fun l space [mk_pvar l var inty] space body
        (Some { t = Tfn (inty, m_outy) }) in
    let result = Monad.mk_bind env l inty m_outy x fn in
    type_eq l "Internal: mk_bind result check" (exp_to_typ result) (m_outy);
    result

  let mk_let (env : env) (l_org : Ast.l) (pat : pat) (v : exp) (code : exp) : exp =
    let l = loc_trans "mk_let [Generic]" l_org in
    mk_choice env l (exp_to_typ code) v [pat, code]
end

module Context_list = Make_Generic_Context(Monad_list)

(* Compilation context for the identity monad.

   Failure is implemented by an exception. *)
module Context_pure = Make_Generic_Context(Monad_pure)

module Context_option = Make_Generic_Context(Monad_option)

module Context_unique = Make_Generic_Context(Monad_unique)

let select_module = function
  | Out_list -> (module Context_list : COMPILATION_CONTEXT)
  | Out_pure -> (module Context_pure : COMPILATION_CONTEXT)
  | Out_unique -> (module Context_unique : COMPILATION_CONTEXT)
  | Out_option -> (module Context_option : COMPILATION_CONTEXT)

(** [get_witness_type env reldescr] extract the witness type from the
    descriptor [reldescr].

    The called should ensure that such a witness type is actually present. *)
let get_witness_type (env : env) (reldescr : reldescr) : Types.t =
  let c = c_env_lookup reldescr.rel_loc env.c_env reldescr.rel_const_ref in
  match c.relation_info with
    | Some { ri_witness = Some (t, _) } ->
      { t = Tapp ([], t) }
    | _ ->
      raise
        (Reporting_basic.
           (Fatal_error (Err_internal
                           (Ast.Unknown, "Impossible to find a witness type."))))

(* [out_ty_from_mode env reldescr spec] extracts the Lem output type
   from the mode specification [spec]. *)
let out_ty_from_mode
    (env : env) (reldescr : reldescr) ((mode, wit, _out) : mode_spec)
  : Types.t =
  let ret = map_filter (function
      | (Rel_mode_out,x) -> Some x
      | _ -> None
    ) (List.map2 (fun x y -> (x,y)) mode reldescr.rel_argtypes) in
  let ret =
    if not wit
    then ret
    else ret @ [ get_witness_type env reldescr ]
  in
  mk_tup_unit_typ ret

(* [in_tys_from_mode env reldescr spec] extracts the Lem input types
   from the mode specification [spec]. *)
let in_tys_from_mode
    (env : env) (reldescr : reldescr) ((mode, _wit, _out) : mode_spec)
  : Types.t list =
  map_filter (function
    | (Rel_mode_in,x) -> Some x
    | _ -> None
  ) (List.map2 (fun x y -> (x,y)) mode reldescr.rel_argtypes)

(* [ty_from_mode env reldescr spec] extracts the Lem type of the
   function from the mode specification [spec]. *)
let ty_from_mode
    (env : env) (reldescr : reldescr) ((_,_,out) as mode : mode_spec)
  : Types.t =
  let args = in_tys_from_mode env reldescr mode in
  let ret = out_ty_from_mode env reldescr mode in
  let module M = (val select_module out : COMPILATION_CONTEXT) in
  multi_fun args (M.mk_type ret)

(**************************************************************************)
(* Compilation                                                            *)
(**************************************************************************)

(** The Compile functor converts code expressed in the monadic
    mini-language into real Lem expressions using a compilation
    context. *)
module Compile(M : COMPILATION_CONTEXT) = struct
  let rec compile_code env ty loc code : exp =
    let l = loc_trans "compile_code" loc in
    match code with
      | RETURN(exps) ->
        let ret = mk_tup_unit_exp l exps in
        M.mk_return env l (exp_to_typ ret) ret
      | IF(cond, code) ->
        let subexp = compile_code env ty loc code in
        M.mk_cond env l ty cond subexp
      | LET(p,e,code) ->
        let subexp = compile_code env ty loc code in
        M.mk_let env l p e subexp
      | CALL(n_ref, inp, outp, code) ->
        let subexp = compile_code env ty loc code in
        let func = cdr_instantiate env l n_ref [] in
        let call = List.fold_left (fun func arg -> mk_app l func arg None)
          func inp in
        let pat = mk_tup_unit_pat l outp in
        M.mk_bind env l (annot_to_typ pat) (exp_to_typ subexp)
          call pat subexp

  let compile_rule env ty (loc, patterns, code) =
    let pattern = mk_tup_unit_pat (loc_trans "compile_rule" loc) patterns in
    let lemcode = compile_code env ty loc code in
    (pattern, lemcode)

  let compile_function env reldescr (n,n_ref,mode,mty,rules) : funcl_aux =
    let l = loc_trans "compile_function" reldescr.rel_loc in
    let output_type = out_ty_from_mode env reldescr mode in
    let gen_name = make_namegen Nset.empty in
    let vars = List.map
      (fun ty -> Name.add_lskip (gen_name (Ulib.Text.of_latin1 "input")), ty)
      (in_tys_from_mode env reldescr mode) in
    let tuple_of_vars = mk_tup_unit_exp l (List.map (fun (var,ty) -> mk_var l var ty) vars) in
    let pats_of_vars = List.map (fun (var,ty) -> mk_pvar_ty l var ty) vars in
    let cases = List.map (compile_rule env output_type) rules in
    (* Generate a list of binds and concat them ! *)
    let body = M.mk_choice env l (M.mk_type output_type) tuple_of_vars cases in
    let annot = { term = Name.add_lskip n;
                  locn = l;
                  typ = mty;
                  rest = () } in
    (annot, n_ref, pats_of_vars, Some(space, t_to_src_t (M.mk_type output_type)), space, body)
end

let compile_function env reldescr
    ((n,((_,_,out_mode) as mode),mty,rules) as _m) =
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
      let Some (c_ref) = Nfmap.apply c_ref_m c_rule in
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
    let mk_descr c_env cname cargs =
      let ty = multi_fun cargs {t=Tapp([],type_path)} in
      let descr =
        const_descr
          ~binding:(Path.mk_path mod_path cname)
          ~type_:ty
          ~env_tag:K_constr
          ~l:l
          () in
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
                   type_target_rep = Target.Targetmap.empty;
                   type_target_sorts = Target.Targetmap.empty
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
    let (head, args) = dest_list_app_exp e in
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
        let check_type = {t=Tfn(witness_type, option_ty (mk_tup_unit_typ ret))} in
        Cdmap.insert defs (reldescr.rel_const_ref, (check_name, check_path, check_type))
  ) Cdmap.empty rels in
  (* Register the functions *)
  Cdmap.fold (fun ctxt rel_ref (cname,cpath,ctype) ->
      let c_descr =
        const_descr
          ~binding:cpath
          ~type_:ctype
          ~env_tag:K_let
          ~l:(loc_trans "gen_witness_check_info" l)
          ~targets:Target.all_targets
          () in
    let c_env, c_ref = c_env_store ctxt.ctxt_c_env c_descr in
    let ctxt = { ctxt with ctxt_c_env = c_env } in
    let ctxt = add_v_to_ctxt ctxt (cname, c_ref) in
    let r_info = c_env_lookup_rel_info l ctxt.ctxt_c_env rel_ref in
    let r_info = {r_info with ri_check = Some c_ref} in
    {ctxt with ctxt_c_env = c_env_update_rel_info l ctxt.ctxt_c_env rel_ref r_info }
  ) ctxt defs

let nset_of_list l = List.fold_left (fun set x -> Nset.add x set) Nset.empty l

(** Generation of the witness checking function. *)
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
        let (head, args) = dest_list_app_exp e in
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
      let ret = mk_some env l
        (mk_tup_unit_exp l rule.rule_args) in
      let genconds_exps = List.map (fun (args,witness_ty,check_ref,witness) ->
        let witness_var = mk_var l (Name.add_lskip witness) witness_ty in
        let rhs = mk_some env l (mk_tup_unit_exp l args) in
        let check_id = { id_path = Id_none None; id_locn = l;
                         descr = check_ref; instantiation = [] } in
        let check_fun = mk_const l check_id None in
        let lhs = mk_app l check_fun witness_var None in
        mk_eq_exp env rhs lhs
      ) relconds in
      let ifconds = auxconds @ genconds_exps in
      let cond =
        List.fold_left (mk_and_exp env) (mk_tf_exp true) ifconds in
      let code = mk_if_exp l cond ret (mk_none env l (remove_option (exp_to_typ ret))) in
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
  let defs = map_filter (fun x -> x) (Nfmap.fold (fun l _ v -> v::l) [] defs) in
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

let report_no_translation
    (reldescr : reldescr) (ruledescr : ruledescr)
    (mode : mode_spec) (print_debug : bool)
  =
  if print_debug then begin
    Format.eprintf "No translation for relation %s, mode %a\n"
      (Name.to_string reldescr.rel_name) pp_mode mode;
    Format.eprintf "Blocking rule is %s\n"  (Name.to_string ruledescr.rule_name)
  end;
  no_translation None

(** [partition_conditions l env conds] partitions the lists of indreln
    conditions [cond] into three separate lists [inds], [eqs] and
    [sides].

    - [inds] contains the conditions of shape [P (x, ...)] where [P]
      is an indreln relation. It is a list of pairs [(relinfo, args)]
      where [relinfo] is the relation information for the relation
      [P], and [args] is the list of arguments [x, ...].

    - [eqs] contains the equality conditions, of shape [x = y]. It is
      a list of pair [(x, y)].

    - [sides] contains the remaining conditions. *)
let partition_conditions
    (l : Ast.l) (env : env) (conds : exp list)
  : (const_descr * rel_info * exp list) list * (exp * exp) list * exp list =
  List.fold_left
    (fun (inds, eqs, sides) exp ->
       let head, args = dest_list_app_exp exp in
       match exp_to_term head, args with
       | Constant { descr = eq_ref }, [ u; v ]
         when eq_ref = eq_const_ref env ->
         (inds, (u, v) :: eqs, sides)
       | Constant { descr = c_ref }, _ ->
         let c_d = c_env_lookup l env.c_env c_ref in
         begin match c_d.env_tag with
           | K_relation ->
             let relinfo = c_env_lookup_rel_info l env.c_env c_ref in
             ( (c_d, relinfo, args) :: inds, eqs, sides)
           | _ -> (inds, eqs, exp :: sides)
         end
       | _ -> (inds, eqs, exp :: sides))
    ([], [], []) conds

let transform_rule
    (env : env) (localrels : relsdescr)
    ((mode, need_wit, out_mode) as full_mode : mode_spec)
    (rel : reldescr) (rule : ruledescr)
    (print_debug : bool) :
  ('a * (Ast.l * pat list * code)) =
  let l = loc_trans "transform_rule" rule.rule_loc in
  (* Stores the dependencies on other indreln translations *)
  let requests = ref [] in
  (* The variables that appears in the rule's [forall] part *)
  let vars = Nfmap.domain (Nfmap.from_list rule.rule_vars) in
  let avoid = ref Nset.empty in
  (* Constructs the patterns for input mode. Used at the end. *)
  let (patterns, initeqs) =
    extract_patterns env avoid rule.rule_args
      (List.map (fun x -> x = Rel_mode_in) mode) in
  (* The variables bound by [patterns] are already known *)
  let initknown = Nmap.domain (pats_to_bound patterns) in
  let gen_witness_name =
    let gen = make_namegen Nset.empty in
    fun () -> gen (Ulib.Text.of_latin1 "witness") in
  let gen_witness_var relinfo =
    match relinfo.ri_witness with
    | None -> None
    | Some(t,_) -> Some(gen_witness_name (), {t=Tapp([],t)})
  in
  let (indconds, usefuleqs, sideconds) =
    partition_conditions l env rule.rule_conds in
  (* Generate the witnesses *)
  let indconds = List.map (fun (c_d, relinfo, args) ->
      c_d, relinfo.ri_fns, args, gen_witness_var relinfo)
      indconds in
  (* map_filter drops relations with no witnesses.
     it's not a problem because if our relation has a witness, all these
     relations must have one *)
  let witness_var_order = map_filter (fun (_, _,_,var) -> var) indconds in
  (* Construct the expressions to return. *)
  (* TODO: We must rename any indreln inside ;-) *)
  let returns =
    map_filter
      (function
        | (Rel_mode_in, _) -> None
        | (Rel_mode_out, r) -> Some r)
      (List.map2 (fun x y -> (x,y)) mode rule.rule_args) in
  (* Add witness if needed. *)
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
  let add_side side x =
    List.fold_left (fun x e ->
        if is_t_exp e then x else IF (e, x))
      x side in
  (* build_code does some stuff. It seems to be generating code
     according to some algorithm. *)
  let rec build_code
      (known : Nset.t)
      indconds
      (sideconds : exp list)
      (eqconds : exp list) (usefuleqs : (exp * exp) list) =
    (* [exp_known e] checks whether all free variables of [e] are in [known]. *)
    let exp_known e = Nfmap.fold (fun b v _ -> b && Nset.mem v known)
        true (exp_to_free e) in
    (* [selected_eqs] are the equality where both sides are currently known. *)
    let (selected_eqs,eqconds2) =
      List.partition (fun e -> exp_known e) eqconds in
    (* [selected_side] are the side conditions that can already be computed. *)
    let (selected_side,sideconds2) =
      List.partition (fun e -> exp_known e) sideconds in
    let rec search_ind notok = function
      | [] ->
        begin match eqconds2,sideconds2 with
          | [], [] when notok = [] && List.for_all exp_known returns ->
            RETURN returns
          | _ ->
            if print_debug then begin
              Format.eprintf "DEBUG: Known variables: ";
              Nset.iter (fun n ->
                  Format.eprintf "%s " (Name.to_string n))
                known;
              Format.eprintf "@.";
              Reporting.print_debug_exp env "Return expressions: " returns;
              Reporting.print_debug_exp env "Equalities conditions: "
                (eqconds2);
              Reporting.print_debug_exp env "Side conditions: "
                sideconds2;
              Format.eprintf "DEBUG: %d notoks@." (List.length notok)
            end;
            report_no_translation rel rule full_mode print_debug
        end
      | ((rel : const_descr),modes,args,wit_var) as c::cs ->
        let inargs = List.map exp_known args in
        let mode_matches ((fun_mode, fun_wit, fun_out_mode),_info) =
          List.for_all (fun x -> x)
            (List.map2 (fun inp m -> inp || m = Rel_mode_out) inargs fun_mode)
          && (not need_wit || fun_wit)
          && (fun_out_mode = out_mode)
        in
        let modes =
          List.sort (fun ((mode, wit, _), _) ((mode', wit', _), _) ->
              let ninputs = List.fold_left (fun nb relmode ->
                  if relmode = Rel_mode_in then nb + 1 else nb) 0 mode in
              let ninputs' = List.fold_left (fun nb relmode ->
                  if relmode = Rel_mode_in then nb + 1 else nb) 0 mode' in
              if ninputs < ninputs' then 1
              else if ninputs > ninputs' then -1
              else if wit && not wit' then 1
              else if wit' && not wit then -1
              else 0) modes in
        (* TODO: Sort it cleverly *)
        match List.filter mode_matches modes with
        | [] -> search_ind (c::notok) cs
        | ((fun_mode, fun_wit, _out_mode), fun_ref) ::ms ->
          (* We must generate this mode *)
          let fun_name = const_descr_ref_to_ascii_name env.c_env fun_ref in
          requests := (rel, fun_name, (fun_mode, fun_wit, _out_mode)) :: !requests;
          let (outputs, equalities) =
            extract_patterns env avoid args
              (List.map (fun m -> m = Rel_mode_out) fun_mode) in
          let bound = Nmap.domain (pats_to_bound outputs) in
          let outputs, bound = match wit_var with
            | Some(wit_name, wit_ty) when fun_wit ->
              outputs @ [mk_pvar l (Name.add_lskip wit_name) wit_ty],
              Nset.add wit_name bound
            | _ -> outputs, bound
          in
          let inputs = map_filter (fun x -> x) (List.map2 (fun exp m ->
              match m with
              | Rel_mode_in -> Some(exp)
              | Rel_mode_out -> None
            ) args fun_mode) in
          CALL (fun_ref, inputs, outputs,
                (build_code (Nset.union bound known)
                   (cs@notok) sideconds2 (equalities@eqconds2) usefuleqs))
    in
    let use_eq usefuleqs u v =
      (* u is known, v is (maybe) unknown *)
      let ([output], equalities) =
        extract_patterns env avoid [v] [true] in
      let bound = Nmap.domain (pat_to_bound output) in
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
    add_side selected_eqs (add_side selected_side (search_eq [] usefuleqs))
  in
  let e =
    build_code initknown indconds sideconds initeqs usefuleqs in
  let seen = ref Nset.empty in
  let (ps, eqs)= linearize env patterns seen avoid in
  (!requests, (l, ps, linearize_code env seen avoid (add_side [mk_and_exps env eqs] e)))

let transform_rules env localrels mode reldescr print_debug =
  List.fold_left (fun (reqs, fns) x ->
      let reqs', fn = transform_rule env localrels mode reldescr x print_debug in
      (List.rev_append reqs' reqs, fn :: fns))
    ([], []) reldescr.rel_rules

(* env is the globalized env *)
(* For each relation : we assume all modes are possible (via updating reldescr)
   and then try to see what mode can effectively computed from that.
   We then try to get the least fixed point
*)
let join f a b = 
  List.concat (List.map (fun x -> List.map (fun y -> f x y ) b) a)

let gen_fns_info_aux l mod_path ctxt rels =
  let env = defn_ctxt_to_env ctxt in
  let l = loc_trans "gen_fns_info" l in
  (*  TODO: list_possible_modes mod_path ctxt rels;  *)
  Nfmap.fold (fun ctxt relname reldescr ->
    let rel_ref = reldescr.rel_const_ref in
    List.fold_left (fun ctxt (name, mode) ->
      let ty = ty_from_mode env reldescr mode in
      let path = Path.mk_path mod_path name in
      let f_descr =
        const_descr
          ~binding:path
          ~type_:ty
          ~env_tag:K_let
          ~targets:Target.all_targets
          ~l:l
          () in
      let c_env, f_ref = c_env_store ctxt.ctxt_c_env f_descr in
      let ctxt = { ctxt with ctxt_c_env = c_env } in
      let ctxt = add_v_to_ctxt ctxt (name, f_ref) in
      let r_info = c_env_lookup_rel_info l ctxt.ctxt_c_env rel_ref in
      let r_info = {r_info with ri_fns = (mode, f_ref)::r_info.ri_fns} in
      {ctxt with ctxt_c_env = c_env_update_rel_info l ctxt.ctxt_c_env rel_ref r_info }
    ) ctxt reldescr.rel_indfns
  ) ctxt rels


let list_possible_modes mod_path ctxt rels =
  (* [all_modes] is a mapping from relation names to a [reldescr] object
     requiring all modes to be generated. *)
  let all_modes =
    let gen_name = make_namegen Nset.empty in
    Nfmap.map (fun relname reldescr ->
      let out_modes = [Out_list] in
      let wit_modes = if reldescr.rel_witness = None then [false] else [false;true] in
      let io_modes = List.fold_left 
        (fun acc _ -> join (fun x y -> x::y) [Rel_mode_in; Rel_mode_out] acc) 
        [[]] reldescr.rel_argtypes in
      let back_map = Hashtbl.create 17 in
      List.iter (fun (name, mdesc) ->
          Hashtbl.add back_map mdesc name)
        reldescr.rel_indfns;
      let modes = join (fun (x,y) z ->
          let name =
            try
              Hashtbl.find back_map (x, y, z)
            with Not_found ->
              gen_name (Ulib.Text.of_latin1 (Name.to_string relname ^ "_indfn")) in
          (name , (x,y,z)))
          (join (fun x y -> (x,y)) io_modes wit_modes) out_modes in
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

let gen_fns_info
    (l : Ast.l) (mod_path : Name.t list)
    (ctxt : defn_ctxt) (names : indreln_name lskips_seplist)
    (rules : indreln_rule lskips_seplist) : defn_ctxt =
  let env = defn_ctxt_to_env ctxt in
  let rels = get_rels env l names rules in
  (* Only generate the modes if there is at least one annotated rule. *)
  let gen =
    Nfmap.fold (fun gen _ reldescr ->
        gen || List.length reldescr.rel_indfns > 0)
      false rels in
  if gen then
    let l = loc_trans "gen_fns_info" l in
    let full_rels = list_possible_modes mod_path ctxt rels in
    gen_fns_info_aux l mod_path ctxt full_rels
  else
    ctxt

let gen_fns_def env l mpath localenv names rules local =
  let rels = get_rels env l names rules in
  let to_transform = ref [] in
  to_transform :=
    Nfmap.fold (fun lst relname reldescr ->
        List.fold_left (fun lst (fn_name, mode) ->
            (reldescr, fn_name, mode) :: lst)
          lst reldescr.rel_indfns)
      [] rels;
  let requests = ref [] in
  let generated = ref [] in
  let transformed = ref [] in
  while !to_transform != [] do
    transformed :=
    List.map (fun (reldescr, name, mode) ->
           generated := (reldescr.rel_name, mode) :: !generated;
           let reqs, transformed_rules = transform_rules env rels mode reldescr true in
           requests := List.rev_append reqs !requests;
           (reldescr, (name, mode, ty_from_mode env reldescr mode, transformed_rules)))
      !to_transform @ !transformed;
    to_transform :=
      map_filter (fun (cd, fun_name, mdescr) ->
          let name = Path.get_name cd.const_binding in
          if List.mem (name, mdescr) !generated
          then None
          else
            match Nfmap.apply rels name with
            | Some reldescr -> Some (reldescr, fun_name, mdescr)
            | None -> raise_error Ast.Unknown "relation missing"
                        (fun ppf (name, mdesc) ->
                           Format.fprintf ppf "%s [%a]" (Name.to_string name)
                             pp_mode mdesc) (name, mdescr))
        !requests;
    requests := [];
  done;
  let transformed_rules = ref Nfmap.empty in
  List.iter (fun (reldescr, data) ->
      match Nfmap.apply !transformed_rules reldescr.rel_name with
      | None ->
        transformed_rules := Nfmap.insert !transformed_rules
            (reldescr.rel_name, (reldescr, [data]))
      | Some (_, datalist) ->
        transformed_rules := Nfmap.remove !transformed_rules reldescr.rel_name;
        transformed_rules :=
          Nfmap.insert !transformed_rules
            (reldescr.rel_name, (reldescr, data :: datalist)))
    !transformed;
  let u,v = compile_to_typed_ast env !transformed_rules in
  let code = u,v,local in
  let emptydef = 
    Nfmap.fold (fun b _ (_,l) -> b && [] = l) true !transformed_rules in
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
