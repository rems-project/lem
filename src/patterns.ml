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
open Typed_ast_syntax
open Target
open Pattern_syntax

let r = Ulib.Text.of_latin1
let space = Some [Ast.Ws (r" ")]
let new_line = Some [Ast.Ws (r"\n")]

module C_no_types = Exps_in_context(struct let env_opt = None let avoid = None end)


(******************************************************************************)
(* Configuration                                                              *)
(******************************************************************************)

(** Configure how many nestings of qantifiers are OK *)
let max_succ_nesting = 5

(** Only these types may be used in number patterns *)
let natural_ty = { Types.t = Types.Tapp ([], External_constants.type_label_to_path "type_natural")  }
let number_pattern_types = [nat_ty; natural_ty]


let check_number_patterns_aux (p : pat) : bool = 
  let is_num_pat = match p.term with
    | P_num_add _ -> false
    | P_lit li -> 
      begin
         match li.term with 
           | L_num _ -> true
           | _ -> false
      end
    | _ -> false
  in
  let _ = if (is_num_pat && not (List.mem p.typ number_pattern_types)) then 
     raise (Reporting_basic.err_type p.locn "number pattern not of type nat or natural") in
  true

let check_number_patterns env p = (for_all_subpat check_number_patterns_aux p; ())



(******************************************************************************)
(* Generating fresh variable names for types                                  *)
(******************************************************************************)

type var_name_generator = Name.t option -> Types.t -> Name.t

let full_var_name_gen (name_set : NameSet.t) (sn : Name.t option) (ty : Types.t) : Name.t =
  let n0 = Util.option_default (Types.t_to_var_name ty) sn in
  let n1 = Name.fresh (Name.to_rope n0) (fun n -> not (NameSet.mem n name_set)) in
n1

let mk_var_name_gen name_set =
  let set_ref = ref name_set in
  let real_fun sn ty =
    let new_n = full_var_name_gen (!set_ref) sn ty in
    let _ = set_ref := NameSet.add new_n (!set_ref) in
    new_n
  in real_fun

(* if p is a variable, the original name is kept, otherwise a new one generated
   based on the type *)
let pattern_gen gen p =
  match dest_var_pat p with
    | Some n -> n
    | None -> gen None (annot_to_typ p)

(******************************************************************************)
(* Auxiliary functions for constructing various types of expressions          *)
(******************************************************************************)

let matrix_compile_mk_pvar n ty =
  let l = Ast.Trans (false, "matrix_compile_mk_pvar", None) in
  C_no_types.mk_pvar l (Name.add_lskip n) ty

let matrix_compile_mk_var n ty =
  let l = Ast.Trans (false, "matrix_compile_mk_var", None) in
  C_no_types.mk_var l (Name.add_lskip n) ty

let matrix_compile_mk_pwild ty =
  let l = Ast.Trans (false, "matrix_compile_mk_pwild", None) in
  C_no_types.mk_pwild l None ty

let matrix_compile_mk_pcons p1 p2 =
  let l = Ast.Trans (true, "matrix_compile_mk_pcons", None) in
  C_no_types.mk_pcons l p1 None p2 (Some (annot_to_typ p2))

let matrix_compile_mk_plist pL ty =
  let l = Ast.Trans (true, "matrix_compile_mk_plist", None) in
  let psl = Seplist.from_list (List.map (fun p -> (p, None)) pL) in
  C_no_types.mk_plist l None psl None ty

let matrix_compile_mk_precord fid pL ty =
  let l = Ast.Trans (true, "matrix_compile_mk_precord", None) in
  let psl = Seplist.from_list (List.map2 (fun (id, _) p -> ((id, None, p), None)) fid pL) in
  C_no_types.mk_precord l None psl None (Some ty)

let matrix_compile_mk_pvar_pwild vs n ty =
  if NameSet.mem n vs then (true, matrix_compile_mk_pvar n ty) else (false, matrix_compile_mk_pwild ty)

let matrix_compile_mk_pvar_pwild_list vs nL tyL =
  let rec aux occ acc vs nL tyL =
   match (nL, tyL) with
         (n :: nL', ty :: tyL') ->
          let (occ_new, p') = matrix_compile_mk_pvar_pwild vs n ty in
          aux (occ || occ_new) (p' :: acc) vs nL' tyL'
	| _ -> (occ, List.rev acc) in
  aux false [] vs nL tyL

(******************************************************************************)
(* Matrix datatype                                                            *)
(******************************************************************************)

(* A row consists of a row number, a list of patterns and an expression. 
   We need to perform substitutions and let bindings on the expression frequently.
   Therefore, it is represented in a special extended form supporting this.
   The exp is preceded by a series of let bindings. These are represented by
   a list of (var, exp) pairs. Moreover, a NameSet is used to distinguish the automatically
   generated variable names from the original ones.*)

type pat_matrix_ext_exp = NameSet.t * (Name.t * exp) list * exp
type pat_matrix_row = int * pat list * pat_matrix_ext_exp

(* A matrix consists of a list of rows as well as the input and a function how to reconstruct the
   original pattern for each row *)
type pat_matrix = exp list * pat_matrix_row list * (pat list -> pat list)


let match_compile_unreachable m =
  Reporting_basic.Fatal_error (Reporting_basic.Err_unreachable(Ast.Unknown, "pattern compilation: "^m))


(******************************************************************************)
(* Some auxiliary stuff on matrixes                                           *)
(******************************************************************************)

let pat_matrix_col_to_front n ((input, rows, pf) : pat_matrix) : pat_matrix =
  (Util.list_to_front n input, 
   List.map (fun (i, pL, ee) -> (i, Util.list_to_front n pL, ee)) rows,
   fun pL -> pf (Util.undo_list_to_front n pL)
  )

let pat_matrix_get_col (n : int) ((input, rows, _) : pat_matrix) : (exp * pat list) =
  (List.nth input n, List.map (fun (_, pL, _) -> List.nth pL n) rows)

let nameset_from_list l = List.fold_left (fun s e -> NameSet.add e s) NameSet.empty l


let pat_matrix_ext_exp_vars (_, let_list, e) = 
  let s0 : NameSet.t = nameset_from_list (List.map (fun (v, _) -> v) let_list) in
  let eL = e :: (List.map (fun (_, e) -> e) let_list) in
  let s = List.fold_left (fun (s : NameSet.t) (e : exp) -> 
       NameSet.union (nfmap_domain (C_no_types.exp_to_free e)) s) s0 eL
  in s

let pat_matrix_vars ((input, rows, _) : pat_matrix) = 
  let s0 = List.fold_left (fun (s : NameSet.t) (e : exp) -> 
       NameSet.union (nfmap_domain (C_no_types.exp_to_free e)) s) NameSet.empty input in
  let add_row_names (_, pL, ee) s0 =
    let s_ee = pat_matrix_ext_exp_vars ee in
    let s_pL = List.fold_left (fun s p -> 
                 NameSet.union (nfmap_domain p.rest.pvars) s) NameSet.empty pL in
    let s_row = NameSet.union s_ee s_pL in
    NameSet.union s0 s_row 
  in
  let s1 = List.fold_left (fun s r -> add_row_names r s) s0 rows in
  s1

let pat_matrix_pats ((_, rows, _) : pat_matrix) : pat list = 
  List.flatten (List.map (fun (_, pL, _) -> pL) rows)


(******************************************************************************)
(* Transforming between matrices and expressions                              *)
(******************************************************************************)

let make_initial_pat_matrix iL peL : pat_matrix =
   (iL, Util.list_mapi (fun i (pL, e) -> (i, pL, (NameSet.empty, [], e))) peL, 
    fun pL -> pL)

(* Transforming a case expression into a matrix *)
let case_exp_to_pat_matrix (flag : bool) (exp:exp) : pat_matrix option = match C_no_types.exp_to_term exp with 
 (Case(c,_,e,_,patexps,_)) -> 
   if flag && c then None else (
   let peL = List.map (fun (p, _, e, _) -> ([p], e)) (Seplist.to_list patexps) in
   Some (make_initial_pat_matrix [e] peL))
 | _ -> None

let case_exp_extract_lskips (exp:exp) : Ast.lex_skips = match C_no_types.exp_to_term exp with 
 (Case(false,s1,e,s2,patexps,s3)) -> 
    let sk_flatten sks = List.fold_right Ast.combine_lex_skips sks None in
    let ws = Seplist.to_sep_list (fun (p, s, e, _) -> Ast.combine_lex_skips (pat_extract_lskips p) s) (fun s -> s) patexps in
    sk_flatten ([s1; s2] @ ws @ [s3])
 | _ -> None


(* Transforming a pattern list into a matrix *)
let pat_list_to_pat_matrix (pL : pat list) : pat_matrix option =
 match pL with [] -> None | p :: pL' -> begin
   let p_ty = annot_to_typ p in
   let dummy_exp = mk_dummy_exp p_ty in
   let peL = List.map (fun p -> ([p], dummy_exp)) pL in
   Some (make_initial_pat_matrix [dummy_exp] peL)
 end


(* Transforming an expression into a matrix, not only case expressions *)
let funcl_aux_list_to_pat_matrix = function
  | ((((_, _, first_pL, _, _, _):funcl_aux)::_) as l) ->
  let iL = List.map (fun p -> mk_dummy_exp(annot_to_typ p)) first_pL in
  let rows = List.map (fun (_, _, pL, _, _, e) -> (pL, e)) l in
  let m = make_initial_pat_matrix iL rows in
  m
  | [] -> assert false

let letbind_to_pat_matrix ((lb, _):letbind) ee =
  match lb with
    | Let_fun (_, pL, _, _, e) -> (false, 
        let iL = List.map (fun p -> mk_dummy_exp(annot_to_typ p)) pL in
        make_initial_pat_matrix iL [(pL, e)])
    | Let_val (p, _, _, e) -> begin
         let m = make_initial_pat_matrix [e] [([p], ee)] in
         (true, m)
      end

let exp_to_pat_matrix (exp:exp) : pat_matrix option = match C_no_types.exp_to_term exp with 
   Case _ -> case_exp_to_pat_matrix false exp
 | Fun (_, pL, _, e) -> begin
     let iL = List.map (fun p -> mk_dummy_exp(annot_to_typ p)) pL in
     let m = make_initial_pat_matrix iL [(pL, e)] in
     Some m
   end
 | Function (_, patexps, _) -> begin
     let ty_fun = exp_to_typ exp in
     let ty = match ty_fun.Types.t with Types.Tfn (_, t) -> t | _ -> 
       raise (match_compile_unreachable "function expression not of function-type") in

     let peL = List.map (fun (p, _, e, _) -> ([p], e)) (Seplist.to_list patexps) in
     if peL = [] then None else
     let m = make_initial_pat_matrix [mk_dummy_exp ty] peL in
     Some m
   end
 | Let (_, lb, _, e) -> let (_, m) = letbind_to_pat_matrix lb e in Some m
 | _ -> None


let letbind_to_defname ((lb, l):letbind) =
  match lb with
      Let_fun (nsa, _, _, _, _) -> Name.strip_lskip (nsa.term)
    | Let_val (p, _, _, _) -> 
         match dest_var_pat p with Some n -> n
           | None -> Name.from_rope (r "_")

let def_to_pat_matrix_list (((d, _), l,_) : def) : (Name.t * (bool * pat_matrix) * Ast.l) list = match  d with 
  |  Val_def ((Fun_def (_, _, _, sl))) -> begin 
       let (_, _, sll) = funcl_aux_seplist_group sl in
       let to_m (n, (sl:funcl_aux lskips_seplist)) = (n, (false, funcl_aux_list_to_pat_matrix (Seplist.to_list sl)), l) in
       List.map to_m sll       
     end
  |  Val_def (Let_inline (_, _, _, nsa, _, nl, _, e)) -> begin 
       let n = Name.strip_lskip (nsa.term) in
       let nsa_to_pvar nsa =
         let ty = annot_to_typ nsa in
         C_no_types.mk_pvar l nsa.term ty
       in   
       let pL = List.map nsa_to_pvar nl in
       let iL = List.map (fun p -> mk_dummy_exp(annot_to_typ p)) pL in
       let m = make_initial_pat_matrix iL [(pL, e)] in
       [(n, (false, m), l)]
     end
  | _ -> []

(* and back again *)
let extended_exp_to_exp ((_, let_list, exp):pat_matrix_ext_exp) : exp =
  let l_org = exp_to_locn exp in
  let l = Ast.Trans (true, "extended_exp_to_exp", Some l_org) in
  let new_sub n m = (Types.TNfmap.empty, Nfmap.insert Nfmap.empty (n, Sub_rename m)) in
  let sub_fun ((n : Name.t), (en : Name.t)) = (C_no_types.exp_subst (new_sub n en)) in

  let modify_fun (n, e) e2 =
     match dest_var_exp e with
       None -> mk_let_exp l (n, e) e2
     | Some en -> sub_fun (n, en) e2 in

  let r = List.fold_right modify_fun let_list exp in
  r

let pat_matrix_to_exp org_l env ((input, rows, _) : pat_matrix) : exp = 
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  let l = Ast.Trans (true, "pat_matrix_to_exp", Some org_l) in
  
  let mk_tup_ty (tyL: Types.t list) : Types.t option = Some ({ Types.t = (Types.Ttup tyL); }) in

  let from_list xL = Seplist.from_list (List.map (fun x -> (x, None)) xL) in
  let in_e = match input with
    | [i'] -> i'
    | _ -> C.mk_tup l None (from_list input) None (mk_tup_ty (List.map exp_to_typ  input))  in
  let row_to_pat_exp ((_, pL, ee) : pat_matrix_row)  =
    let p = match pL with
      | [p'] -> p'
      | _ -> C.mk_ptup l None (from_list pL) None (mk_tup_ty (List.map annot_to_typ pL)) in
    let e = extended_exp_to_exp ee in
    (p, e) in
  let rows' = List.map row_to_pat_exp rows  in
  let typ = match rows with
               (_, _, (_, _, e)) :: _ -> exp_to_typ e
             | _ -> raise (match_compile_unreachable "empty matrix in pat_matrix_to_exp") in
  mk_case_exp true l in_e rows' typ


(* If the matrix is trivial, the transformation is simpler *) 
let is_trivial_pat_matrix (m : pat_matrix) : bool = match m with 
   (_, (_, pat_list, _) :: rows, _) -> List.for_all (fun p -> is_var_pat p || is_wild_pat p) pat_list
 | _ -> false

let is_empty_pat_matrix (m : pat_matrix) : bool = match m with 
   (_, [], _) -> true
 | _ -> false

let pat_matrix_to_typ (m:pat_matrix) : Types.t = 
  match m with 
    | (_, [], _) -> raise (match_compile_unreachable "pat_matrix_to_typ called on empty matrix")
    | (_, (_, _, (_, _, e)) :: _, _) -> exp_to_typ e

let pat_matrix_to_pat ((iL, _, pf):pat_matrix) : pat list = 
  let pL = List.map (fun i -> matrix_compile_mk_pwild (exp_to_typ i)) iL in
  pf pL


let add_to_ext_exp ((gen_vars, let_list, exp) : pat_matrix_ext_exp) (v : Name.t) (e : exp) : pat_matrix_ext_exp =
  let (let_list', exp') =  if not (NameSet.mem v gen_vars) then 
    begin
      let vs = pat_matrix_ext_exp_vars (gen_vars, let_list, exp) in
      (if (NameSet.mem v vs) then
         ((v,e) :: let_list, exp)
       else 
         (let_list, exp))
    end else
    begin
      let real_sub = (Types.TNfmap.empty, Nfmap.insert Nfmap.empty (v, Sub e)) in
      let sub_fun (v, e) = (v, C_no_types.exp_subst real_sub e) in
      (List.map sub_fun let_list, exp)
    end in
  (gen_vars, let_list', exp)


let trivial_pat_matrix_to_exp (m : pat_matrix) : exp =
  let _ = if is_trivial_pat_matrix m then () else 
             raise (match_compile_unreachable "trivial_pat_matrix_to_exp called on non-trivial matrix") in 
  match m with 
    (input, (_, pats, ee) :: _, _) -> 
      let process_fun ee e p = match p.term with
         P_wild _ -> ee
       | P_var ns -> add_to_ext_exp ee (Name.strip_lskip ns) e 
       | _ -> raise (match_compile_unreachable "trivial matrix contains other patterns than var and wildcards")
      in  
      let _ = assert (List.length input = List.length pats) in
      let ee' = List.fold_left2 process_fun ee input pats in
        extended_exp_to_exp ee'  
  | _ -> raise (match_compile_unreachable "trivial matrix is empty")


(******************************************************************************)
(* Simplifications of the matrix                                              *)
(******************************************************************************)

(* A matrix simplification that is supposed to preserve semantics. 
   For example, patterns are simplified by explicitly transforming "as"-patterns.
   Or tuples are split. *)
type pat_matrix_simp = pat_matrix -> pat_matrix option

let pat_matrix_simp_pat l_org ((input, rows, pf) : pat_matrix) : pat_matrix option =
  let l = Ast.Trans (true, "pat_matrix_simp_pat", Some l_org) in
  let pat_simp (p:pat) (i:exp) (ee : pat_matrix_ext_exp) = 
      match p.term with
      | P_wild _ -> None
      | P_as(_,p,_,(n, _),_) -> Some (p , add_to_ext_exp ee (Name.strip_lskip n) i)
      | P_typ(_,p,_,_,_) -> Some (p, ee)
      | P_var(n) -> Some (C_no_types.mk_pwild l None (annot_to_typ p), add_to_ext_exp ee (Name.strip_lskip n) i)
      | P_var_annot(n,t) ->  Some (C_no_types.mk_pvar l n (annot_to_typ p), ee)
      | P_const _ -> None
      | P_backend _ -> None
      | P_record _ -> None
      | P_vector _ -> None
      | P_vectorC _ -> None
      | P_tup _ -> None
      | P_list _ -> None
      | P_num_add ((n,_), _, _, i) -> if i > 0 then None else Some (C_no_types.mk_pvar l n p.typ, ee)
      | P_paren(_,p,_) ->  Some (p, ee)
      | P_cons _ -> None
      | P_lit(li) ->
           match li.term with 
               L_unit (s1, s2) -> Some (C_no_types.mk_pwild l (Ast.combine_lex_skips s1 s2) (annot_to_typ p), ee)
             | _ -> None
  in
  let rec pat_simp_iter p i (ee, b) =
    match pat_simp p i ee with
        None -> (p, (ee, b))
      | Some (p', ee') -> pat_simp_iter p' i (ee', true) in
  let rec row_simp b iL ((row_no,patL, ee):pat_matrix_row) = match (patL, iL) with
        ([], _) -> ((row_no,patL, ee), b)
      | (p :: patL', i :: iL') -> 
          let (p', (ee', b')) = pat_simp_iter p i (ee, b) in
          let ((row_no', patL'', ee''), b'') = row_simp b' iL' (row_no,patL', ee') in
          ((row_no', p' :: patL'', ee''), b'') 
      | _ -> raise (Failure "pat_matrix_simp_pat: Matrix not well-formed!")
  in
  let rows' = List.map (row_simp false input) rows in
  if (List.exists (fun (_, b) -> b) rows') then
     Some (input, List.map (fun (r, _) -> r) rows', pf)
  else None
  
let rec pat_matrix_simps_combine (sL : pat_matrix_simp list) m =
  match Util.option_first (fun s -> s m) sL with 
      None -> m
    | Some m' -> pat_matrix_simps_combine sL m'

let pat_matrix_simps l_org = pat_matrix_simps_combine [pat_matrix_simp_pat l_org]
   


(******************************************************************************)
(* The real compilation step                                                  *)
(******************************************************************************)

(* A compilation step is represented very abstractly here. A "matrix_compile_fun" is given
   a column of the matrix. It then checks whether it can do one compilation step. If it can't, it returns None.
   Otherwise, it returns a collection of functions needed to perform the step.
   
   Essentially, a compilation step performs one case distinction at top level. The cases-function
   is described by "matrix_compile_top_fun". It gets the input and performs a case split on this.
   What it should do in each case is passed as the second argument. Since there might be an arbitrary
   number of cases, this is passed as a list of expressions. Since the original pattern match might not
   have been complete, there might be undefined cases. Therefore, it in fact gets only a list of expression
   options and also returns an option to express that the result is undefined in every case. 

   It remains to decide, what to do in each of these cases. For this, the "matrix_compile_fun" returns
   a pair of "matrix_compile_case_fun" and "matrix_compile_case_dest_in" for each case. 
   The "matrix_compile_case_fun" explains what to do with a row in the old matrix, i.e.
   given the old pattern and the old expression, it tells whether to keep that row and
   in case it is kept, how to split the old pattern into a list of patterns and
   how to modify the expression. "matrix_compile_case_dest_in" says how to modify the input of the matrix
   for each case.

   Finally, "matrix_compile_in_case" checks whether the input only matches one case anyhow and
   therefore no case split should be performed. 

   More details about this algorithm can be found in a high-level Isabelle formalisation
   in "notes/pattern_compile.thy" and the note "notes/notes10-2012-12-pattern_compile.txt"
*)


type matrix_compile_top_fun = exp -> exp list -> exp
type matrix_compile_case_fun = pat -> pat_matrix_ext_exp -> (pat list * pat_matrix_ext_exp) option
type matrix_compile_case_dest_in = exp -> exp list
type matrix_compile_in_case = exp -> (int * exp list) option
type matrix_compile_pattern_reconstruct_fun = pat list -> pat

type matrix_compile_fun = 
 pat list -> 
   (matrix_compile_top_fun * 
      (matrix_compile_case_fun * 
       matrix_compile_case_dest_in * 
       matrix_compile_pattern_reconstruct_fun) 
    list * 
    matrix_compile_in_case) 
 option

(* This exception is used, to tell that no matrix_compile_fun could do anything and 
   therefore the combination of patterns can't be handled. *)
exception Pat_Matrix_Compile_Failed of pat list

let pat_matrix_compile_step_case ((input, rows, pf) : pat_matrix) (new_iL_opt : exp list option) 
   ((pat_fun : matrix_compile_case_fun), 
    (dest_in : matrix_compile_case_dest_in), 
    (restr_pat : matrix_compile_pattern_reconstruct_fun)) : int list * pat_matrix =
   match input with [] -> raise (Failure "pat_matrix_compile_step_fun: empty input") | i :: iL ->
   let new_input0 = (match new_iL_opt with Some iL' -> iL' | None -> dest_in i) in 
   let new_col_count = List.length new_input0 in
   let new_input = new_input0 @ iL in

   let process_row (row_no, pat_list, ee) = 
     match pat_list with [] -> raise (Failure "pat_matrix_compile_step_fun: matrix not well-formed") | p :: pL ->
     match (pat_fun p ee) with
        None -> (Some row_no, None)
      | Some (pL', ee') -> (None, Some (row_no, pL' @ pL, ee'))
   in
   let new_rows_org = List.map process_row rows in
   let new_rows = Util.map_filter (fun (_, x) -> x) (new_rows_org) in
   let skipped_rows = Util.map_filter (fun (x, _) -> x) (new_rows_org) in
   let new_pf pL = let (pL1, pL2) = Util.split_after new_col_count pL in
                          pf ((restr_pat pL1) :: pL2) in
   (skipped_rows, (new_input, new_rows, new_pf))

let pat_matrix_compile_step (cf : matrix_compile_fun) (col_no : int) (m : pat_matrix) : ((exp list -> exp) * ((int list * pat_matrix) list)) =
  let m_resort = pat_matrix_col_to_front col_no m in
  let (i, pL) = pat_matrix_get_col 0 m_resort in 
  match cf pL with
      None -> raise (Pat_Matrix_Compile_Failed pL) (* cf could not handle pL. This is a missing feature. Report it! *)
    | Some (top_fun, (caseL : (matrix_compile_case_fun * matrix_compile_case_dest_in * matrix_compile_pattern_reconstruct_fun) list), (def_dest_in: matrix_compile_in_case)) ->
      begin
          match (def_dest_in i) with
            | Some (i, iL) -> (List.hd, [pat_matrix_compile_step_case m_resort (Some iL) (List.nth caseL i)])
            | None -> (top_fun i, List.map (pat_matrix_compile_step_case m_resort None) caseL)
      end


let pat_matrix_compile_find_col (m: pat_matrix) : int =
  let res_opt = 
    match m with
        (_, ((_, pL, _) :: _), _) -> Util.list_index (fun p -> not (is_var_wild_pat p)) pL         
      | _ -> None in
  match res_opt with
      Some n -> n
    | None -> raise (match_compile_unreachable "pat_matrix_compile_find_col called on empty or trivial matrix")

(******************************************************************************)
(* Matrix Compile Funs                                                        *)
(******************************************************************************)

(* It remains to write actual compile funs. These may be target dependend and
   new ones might add additional features in the future. *)

(* [Pat_Matrix_Compile_Fun_Failed] is used exclusively by matrix_compile_funs to
   state that this functions can't handle the matrix. *)
exception Pat_Matrix_Compile_Fun_Failed

(* An auxiliary function that makes writing compile funs much simpler, because
   the control flow can be simplified by throwing this exception whenever something
   goes wrong. It is catched by the combine function and mapped to None *)
let matrix_compile_fun_check b = if b then () else raise Pat_Matrix_Compile_Fun_Failed
let matrix_compile_fun_get o = Util.option_get_exn Pat_Matrix_Compile_Fun_Failed o

let combine_matrix_compile_fun l (gen : var_name_generator) (matrix_ty : Types.t) (cfL: (var_name_generator -> Types.t -> Ast.l -> matrix_compile_fun) list) : matrix_compile_fun =
  (fun pL -> Util.option_first (fun cf -> try cf gen matrix_ty l pL with Pat_Matrix_Compile_Fun_Failed -> None) cfL)

(* First one for simple tuples *)
let tuple_matrix_compile_fun env (gen : var_name_generator) (m_ty : Types.t) l_org : matrix_compile_fun = fun pL ->

  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in

  (******************)
  (* initial checks *)
  (******************)
  (* get some typle pattern p, store it's length in l and check
     whether every pattern is a tuple pattern of this length of a
     wild-card. Variable patterns can be ignored, because
     simplification replaces them with wildcard ones. After checking
     all the patterns, check the type as well. *)
  let ((p : pat), l) = matrix_compile_fun_get (Util.option_first (fun p -> Util.option_map (fun pL' -> (p, List.length pL')) (dest_tup_pat None p)) pL) in
  let _ = matrix_compile_fun_check (List.for_all (fun p -> (is_tup_pat (Some l) p || is_wild_pat p)) pL) in

  let tyL = matrix_compile_fun_get (match (annot_to_typ p).Types.t with Types.Ttup tyL -> Some tyL | _ -> None) in
  let _ = matrix_compile_fun_check (List.length tyL = l) in
  let loc = Ast.Trans (true, "tuple_matrix_compile_fun", Some l_org) in

  (* build auxiliary variables, pattern variables and wildcards *)
  let new_var_nameL = (
     match dest_tup_pat None p with
         None -> (* Can't use old pattern names, so instead use type information *) List.map (gen None) tyL 
       | Some pL -> (* Try to reuse old names *) List.map (pattern_gen gen) pL) in
  let new_pwcL = List.map matrix_compile_mk_pwild tyL in
  let new_varL = List.map2 matrix_compile_mk_var new_var_nameL tyL in
  
  (* Build top-fun *)
  let build_tup_pat patL = C.mk_ptup loc None (Seplist.from_list (List.map (fun p -> (p, None)) patL)) None (Some (annot_to_typ p)) in
  let top_fun : matrix_compile_top_fun  = fun i eL -> match eL with
  | [e] ->
     let vs = nfmap_domain (C.exp_to_free e) in
     let (used, new_pL) = matrix_compile_mk_pvar_pwild_list vs new_var_nameL tyL in
     if not used then e else mk_case_exp true loc i [(build_tup_pat new_pL, e)] m_ty
  | _ -> assert false
  in

  (* build functions for the only case *)
  let case_fun p ee = if is_wild_pat p then Some (new_pwcL, ee) else
                      (Util.option_map (fun pL' -> (pL', ee)) (dest_tup_pat (Some l) p)) in

  let dest_in e = new_varL in

  (* build default case *)
  let in_case e = match dest_tup_exp (Some l) e with None -> None | Some iL -> Some (0, iL) in
  
  Some (top_fun, [(case_fun, dest_in, build_tup_pat)], in_case)


(* And one for booleans *)
let bool_matrix_compile_fun (gen_match : bool) (gen : var_name_generator) (m_ty : Types.t) l_org : matrix_compile_fun = fun pL ->
  let _ = matrix_compile_fun_check (List.exists is_tf_pat pL) in
  let _ = matrix_compile_fun_check (List.for_all (fun p -> (is_tf_pat p || is_wild_pat p)) pL) in
  let loc = Ast.Trans (true, "bool_matrix_compile_fun", Some l_org) in

  (* Build top-fun *)
  let top_fun : matrix_compile_top_fun  = fun i eL -> match eL with
  | [e_t; e_f] ->
     if gen_match then
       mk_case_exp true loc i [(mk_tf_pat true, e_t); (mk_tf_pat false, e_f)] m_ty
     else
       mk_if_exp loc i e_t e_f
  | _ -> assert false
  in

  (* build functions for the only case *)
  let case_fun b p ee = 
     let check = is_wild_pat p || (if b then is_t_pat p else is_f_pat p) in
     if check then Some ([], ee) else None in

  let dest_in e = [] in
  
  Some (top_fun, [(case_fun true,  dest_in, fun _ -> mk_tf_pat true); 
                  (case_fun false, dest_in, fun _ -> mk_tf_pat false)], fun e -> None)


(* lists *)
let list_matrix_compile_fun env (gen : var_name_generator) (m_ty : Types.t) l_org : matrix_compile_fun = fun pL ->
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  let _ = matrix_compile_fun_check (List.exists (fun p -> (is_cons_pat p || is_list_pat None p)) pL) in
  let _ = matrix_compile_fun_check (List.for_all (fun p -> (is_cons_pat p || is_list_pat None p || is_wild_pat p)) pL) in
  let loc = Ast.Trans (true, "list_matrix_compile_fun", Some l_org) in

  let p = List.hd pL in
  let list_ty = annot_to_typ p in
  let elem_ty = match list_ty.Types.t with 
    | Types.Tapp ([e], _) -> e 
    | _ -> raise Pat_Matrix_Compile_Fun_Failed 
  in

  (* build auxiliary variables, pattern variables and wildcards *)
  let new_list_wc_pat = matrix_compile_mk_pwild list_ty in
  let new_elem_wc_pat = matrix_compile_mk_pwild elem_ty in
  let new_list_var_name = gen None list_ty in
  let new_elem_var_name = gen None elem_ty in
 
  (* Build top-fun *)
  let top_fun : matrix_compile_top_fun  = fun i eL -> match eL with
  | [e_nil; e_cons] ->
     let vs_cons = nfmap_domain (C.exp_to_free e_cons) in
     let (_, cons_p1) = matrix_compile_mk_pvar_pwild vs_cons new_elem_var_name elem_ty in
     let (_, cons_p2) = matrix_compile_mk_pvar_pwild vs_cons new_list_var_name list_ty in
     let cons_p = matrix_compile_mk_pcons cons_p1 cons_p2 in
     let nil_p = matrix_compile_mk_plist [] list_ty in
     mk_case_exp true loc i [(nil_p, e_nil); (cons_p, e_cons)] m_ty
  | _ -> assert false
  in
  
  let restr_pat_nil (l: pat list) = matrix_compile_mk_plist [] list_ty in
  let restr_pat_cons = function 
      [p1;p2] -> matrix_compile_mk_pcons p1 p2 
    | _ -> raise (match_compile_unreachable "list_matrix_compile_fun wrong no of args to rest_pat_cons")
  in

  (* build functions for the only case *)
  let case_fun_nil p ee = 
    if (is_wild_pat p || is_list_pat (Some 0) p) then Some ([], ee) else None 
  in
  let case_fun_cons p ee = match p.term with
      | P_wild _ -> Some ([new_elem_wc_pat; new_list_wc_pat], ee)
      | P_cons _ -> begin
                      let (pe, pL) = matrix_compile_fun_get (dest_cons_pat p) in
                      Some ([pe; pL], ee)
                    end
      | P_list _ -> begin
                      let pL = matrix_compile_fun_get (dest_list_pat None p) in
                      match pL with [] -> None
                                  | (p :: pL') -> Some ([p; matrix_compile_mk_plist pL' list_ty], ee)
                    end
      | _ -> None
  in
  let dest_in_nil e = [] in
  let dest_in_cons e = [matrix_compile_mk_var new_elem_var_name elem_ty; matrix_compile_mk_var new_list_var_name list_ty] in

  (* build default case *)
  Some (top_fun, [(case_fun_nil, dest_in_nil, restr_pat_nil); (case_fun_cons, dest_in_cons, restr_pat_cons)], fun e -> None)


(* constructors *)

(** [make_id mp n inst c] create an id for the the reference [c] with instantiation [inst] and
    stored under module path [mp] and name [n]. *)
let make_id (mp: Name.t list option) (n : Name.t) inst (c:const_descr_ref) : (const_descr_ref id) =
  let loc = Ast.Trans (true, "constr_matrix_compile_make_id", None) in
  let id_p = match mp with None -> Id_none None | Some mp -> Id_some (Ident.mk_ident None mp n) in
  { id_path = id_p;
    id_locn = loc;
    descr = c;
    instantiation = inst }


let constr_matrix_compile_fun (targ : Target.target) (simp_input: bool) (env : env) (gen : var_name_generator) (m_ty : Types.t) l_org : matrix_compile_fun = fun pL ->
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in

  let ((p : pat), p_id) = matrix_compile_fun_get (Util.option_first (fun p -> Util.option_map (fun (id, _) -> (p, id)) (dest_const_pat p)) pL) in
  let _ = matrix_compile_fun_check (List.for_all (fun p -> (is_const_pat p || is_wild_pat p)) pL) in
  let loc = Ast.Trans (true, "constr_matrix_compile_fun", Some l_org) in
  let p_ty = annot_to_typ p in  

  (* get the family of constructors to match against *)
  let cfam = begin 
    let (refl : const_descr_ref list) = Util.map_filter (fun p -> Util.option_map (fun (id, _) -> id.descr) (dest_const_pat p)) pL in
    let cfam_canditates = Types.type_defs_get_constr_families loc env.t_env targ p_ty p_id.descr in
    let cfam_ok cfam = Util.list_subset refl cfam.Types.constr_list in
    matrix_compile_fun_get (Util.option_first (fun cfam -> if cfam_ok cfam then Some cfam else None) cfam_canditates)
  end in

  (* instantiate the family for the matrix type *)
  let (constr_ids, top_fun_opt) = Util.option_get_exn Pat_Matrix_Compile_Fun_Failed (constr_family_to_id loc env p_ty cfam) in

  (* OK, we have the family now, now let's get the instantiation and the right arguments *)
  let all_args = begin
    let build_args (c_id : const_descr_ref id) =
      let cd = c_env_lookup loc env.c_env c_id.descr in   
      let subst = Types.TNfmap.from_list2 cd.const_tparams c_id.instantiation in
      let c_type = Types.type_subst subst cd.const_type in
      let (arg_tyL, _) = Types.strip_fn_type None c_type in
      let resL = List.map (fun ty -> (ty, gen None ty, matrix_compile_mk_pwild ty)) arg_tyL in
      (c_id, resL)
    in List.map build_args constr_ids
  end in

  (* Build top-fun *)
  let top_fun : matrix_compile_top_fun  = begin  
     let dest_eL eL = begin
        let (eL, ed_opt) = if (cfam.Types.constr_exhaustive) then (eL, None) else
            let (eL', e) = Util.list_dest_snoc eL in (eL', Some e) 
        in
        let _ = matrix_compile_fun_check (List.length eL = List.length all_args) in
        (eL, ed_opt)
     end in

     let top_fun_default i eL ed_opt =
        let build_row (c, argL) ee = 
        begin
          let vs = nfmap_domain (C.exp_to_free ee) in
          let build_arg (ty, n, _) = (let (_, p) = matrix_compile_mk_pvar_pwild vs n ty in p) in
          let arg_pL = List.map build_arg argL in
          let full_pat = C.mk_pconst loc c arg_pL (Some p_ty) in
          (full_pat, ee)
        end in

        let pl = List.map2 build_row all_args eL in
        let pl' = match ed_opt with None -> pl | Some ee ->(pl @ [(matrix_compile_mk_pwild p_ty, ee)]) in
        mk_case_exp true loc i pl' m_ty
     in

     let top_fun_special f_id i eL ed_opt = begin
        let build_exp (c, argL) ee = 
        begin
          let vs = nfmap_domain (C.exp_to_free ee) in
          let build_arg (ty, n, _) = (let (_, p) = matrix_compile_mk_pvar_pwild vs n ty in p) in
          let arg_pL = List.map build_arg argL in
          let fun_ee = if (Util.list_null arg_pL) then ee else (C.mk_fun loc None arg_pL None ee None) in
          fun_ee
        end in

        let pl = List.map2 build_exp all_args eL in
        let pl' = match ed_opt with None -> pl | Some ee ->(pl @ [ee]) in

        let f_exp = begin
          let fd = c_env_lookup loc env.c_env f_id.descr in
          let f_ty = Types.type_subst (Types.TNfmap.from_list2 fd.const_tparams f_id.instantiation) fd.const_type in
          C.mk_const loc f_id (Some f_ty)
        end in
        let mk_app_exp e1 e2 = begin
           let b_ty = match Types.dest_fn_type (Some env.t_env) (exp_to_typ e1) with
             | None -> raise (Reporting_basic.err_type loc "non-function in application")
             | Some (arg_ty, b_ty) -> b_ty
           in
           C.mk_app loc e1 e2 (Some b_ty)
        end in
        let rec mk_list_app_exp f aL = begin
          match aL with 
          | [] -> f
          | a :: aL' -> mk_list_app_exp (mk_app_exp f a) aL'
        end in
        mk_list_app_exp f_exp (i::pl')
     end

     in fun i eL -> begin
        let (eL, ed_opt) = dest_eL eL in
        match top_fun_opt with
          | None -> top_fun_default i eL ed_opt
          | Some f_fun -> top_fun_special (f_fun m_ty) i eL ed_opt
     end
  end in
  

  let restr_pat (id, _) pL = C.mk_pconst loc id (List.map mk_opt_paren_pat pL) (Some p_ty) in
  let restr_pat_else _ = matrix_compile_mk_pwild p_ty in

  let case_fun (id, argL) p ee = match p.term with
      | P_wild _ -> Some (List.map (fun (_, _, wcp) -> wcp) argL, ee)
      | P_const (id', pL) -> if (id.descr = id'.descr) then (Some (pL, ee)) else None
      | _ -> None
  in
  let dest_in (id, argL) = 
    let vL = List.map (fun (ty, n, _) -> matrix_compile_mk_var n ty) argL in
    fun e -> vL
  in
  let case_fun_else p ee = 
    if (is_wild_pat p) then Some ([], ee) else
    match dest_const_pat p with 
      | None -> None
      | Some (id, _) -> if List.mem id.descr cfam.Types.constr_list then None else Some ([], ee)
  in
  let dest_in_else e = [] in

  (* build default case *)
  let strip_app e = 
    let rec aux acc e = match C.exp_to_term e with
      | App (e1, e2) -> aux (e2 :: acc) e1
      | _ -> (e, List.rev acc)
    in aux [] e
  in

  let in_case e = let (e', eL) = strip_app e in match C.exp_to_term e' with
      | Constant id' -> begin
          let pos_opt = Util.list_index (fun (id, _) -> (id.descr = id'.descr)) all_args in
          match pos_opt with None -> None
            | Some i -> Some (i, eL)
          end
      | _ -> None 
  in
  
  Some (top_fun, 

        (let funs = List.map (fun x -> (case_fun x, dest_in x, restr_pat x)) all_args in
        if (cfam.Types.constr_exhaustive) then funs else funs @ [(case_fun_else, dest_in_else, restr_pat_else)]),
         
        if simp_input then in_case else (fun e -> None))


(* Record patters *)

let record_matrix_compile_fun (env : env) (gen : var_name_generator) (m_ty : Types.t) l_org : matrix_compile_fun = fun pL ->
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  let ((p : pat), field_p_list) = matrix_compile_fun_get (Util.option_first (fun p -> Util.option_map (fun l -> (p, l)) (dest_record_pat p)) pL) in
  let _ = matrix_compile_fun_check (List.for_all (fun p -> (is_record_pat p || is_wild_pat p)) pL) in
  let loc = Ast.Trans (true, "record_matrix_compile_fun", Some l_org) in

  let p_ty = annot_to_typ p in  
  let inst = match p_ty with 
    | { Types.t = Types.Tapp(args, _) } -> args
    | _ -> raise Pat_Matrix_Compile_Fun_Failed (* should not happen, since reconstor types should be all basic *)
  in
  let first_id = match (List.hd field_p_list) with (fid, _) -> fid in
  let module_path_opt : Name.t list option = match first_id.id_path with Id_none _ -> None | Id_some i -> Some (fst (Ident.to_name_list i)) in

  (* figure out which fields are really needed *)
  let needed_fields = begin
    let fipL =  List.flatten (Util.map_filter dest_record_pat pL) in
    let fL = List.map (fun (fi, _) -> fi.descr) fipL in
    let dL = Util.remove_duplicates fL in
    dL
  end in

  let needed_ids_descr = begin
    let build_id (c : const_descr_ref) =
      let cd = c_env_lookup loc env.c_env c in   
      let c_id =  make_id module_path_opt (Path.get_name cd.const_binding) inst c in
      (c_id, cd)
    in 
    List.map build_id needed_fields
  end in

  (* now build the real argument types and fresh variable names for the arguments *)
  let record_var_name = gen None p_ty in
  let record_var = matrix_compile_mk_var record_var_name p_ty in

  let id_process_fun ((fi : const_descr_ref id), (f_d : const_descr)) = begin
    let subst = Types.TNfmap.from_list2 f_d.const_tparams fi.instantiation in
    let ty_field = match Types.dest_fn_type (Some env.t_env) (Types.type_subst subst f_d.const_type) with
      | Some (_, ty) -> ty
      | _ -> raise (match_compile_unreachable "not a record type")
    in
    let f_exp = C.mk_field loc record_var None fi (Some ty_field) in
    let f_wc = matrix_compile_mk_pwild ty_field in
    (fi, ty_field, f_exp, f_wc) 
  end in
  let ext_ids = List.map id_process_fun needed_ids_descr in

  (* build auxiliary variables, pattern variables and wildcards *)

  (* Build top-fun *)
  let top_fun : matrix_compile_top_fun  = fun i eL -> match eL with
  | [e] ->
    begin match dest_var_exp i with
        None   -> mk_let_exp loc (record_var_name, i) e
      | Some n -> 
          let new_sub n m = (Types.TNfmap.empty, Nfmap.insert Nfmap.empty (n, Sub_rename m)) in
          C.exp_subst (new_sub record_var_name n) e 
    end
  | _ -> assert false
  in

  let restr_pat pL = matrix_compile_mk_precord needed_ids_descr pL p_ty in

  let case_fun p ee = match p.term with
      | P_wild _ -> Some (List.map (fun (_, _, _, f_wc) -> f_wc) ext_ids, ee)
      | P_record _ -> 
        begin
          let fipL = matrix_compile_fun_get (dest_record_pat p) in
          let find_exp (f_i, _, _, f_wc) =
          begin
            let res = try Some (List.find (fun (fid, p) -> (fid.descr = f_i.descr)) fipL) with Not_found -> None in
            match res with None -> f_wc | Some (_, p) -> p
          end
          in Some (List.map find_exp ext_ids, ee)
        end
      | _ -> None
  in

  let dest_in e = List.map (fun (_, _, f_exp, _) -> f_exp) ext_ids in
 
  Some (top_fun, [case_fun, dest_in, restr_pat], fun e -> None)


(* Infinite case statements (for numbers and strings) *)
let cases_matrix_compile_fun dest_pat make_lit (gen_match : bool) env (gen : var_name_generator) (m_ty : Types.t) l_org : matrix_compile_fun = fun pL ->
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  let _ = matrix_compile_fun_check (List.exists (fun p -> not (dest_pat p = None)) pL) in
  let _ = matrix_compile_fun_check (List.for_all (fun p -> ((not (dest_pat p = None)) || is_wild_pat p)) pL) in
  let p_ty = annot_to_typ (List.hd pL) in

  let loc = Ast.Trans (true, "cases_matrix_compile_fun", Some l_org) in
  let constL = Util.remove_duplicates (Util.map_filter dest_pat pL) in 
  
  (* Build top-fun *)
  let top_fun_if : matrix_compile_top_fun  = fun i eL -> 
     let (i', _) = alter_init_lskips remove_init_ws i in
     let _ = matrix_compile_fun_check (List.length eL = (List.length constL + 1)) in
     let rec aux cL eL = match (cL, eL) with 
         ([], [e]) -> e
       | (c::cs, e::es) ->                        
          let c_lit = make_lit p_ty c in
          let c_exp = C.mk_lit loc c_lit (Some p_ty) in
          let eq_exp = mk_eq_exp env i' c_exp in
          mk_if_exp loc eq_exp e (aux cs es)
       | _ -> raise Pat_Matrix_Compile_Fun_Failed (* Should not happen *)
     in aux constL eL
  in
  let top_fun_case : matrix_compile_top_fun  = fun i eL -> 
     let (i', _) = alter_init_lskips remove_init_ws i in
     let _ = matrix_compile_fun_check (List.length eL = (List.length constL + 1)) in
     let pL = (List.map (fun c-> 
          let c_lit = make_lit p_ty c in
          let c_pat = C.mk_plit loc c_lit (Some p_ty) in
          c_pat) constL) @ [matrix_compile_mk_pwild p_ty] in
     mk_case_exp true loc i' (List.combine pL eL) m_ty
  in
  let top_fun = if gen_match then top_fun_case else top_fun_if in

  let restr_pat c _ =
     let c_lit = make_lit p_ty c in
     C.mk_plit loc c_lit (Some p_ty)
  in  
  let restr_pat_else _ = matrix_compile_mk_pwild p_ty in

  let case_fun_const c p ee = 
     let check = is_wild_pat p || (dest_pat p = Some c) in
     if check then Some ([], ee) else None in

  let case_fun_else p ee = 
    if (is_wild_pat p) then Some ([], ee) else
    match dest_pat p with None -> None
      | Some c -> if List.mem c constL then None else Some ([], ee)
  in
  let dest_in e = [] in

  Some (top_fun, (List.map (fun c -> (case_fun_const c, dest_in, restr_pat c)) constL) @ 
                 [(case_fun_else, dest_in, restr_pat_else)], fun e -> None)


let num_matrix_compile_fun =
  let l = Ast.Trans (true, "num_matrix_compile_fun", None) in
  cases_matrix_compile_fun (dest_num_pat) (fun num_ty c -> (C_no_types.mk_lnum l None c None num_ty))

let string_matrix_compile_fun =
  let l = Ast.Trans (true, "string_matrix_compile_fun", None) in
  cases_matrix_compile_fun (dest_string_pat) (fun ty c -> (C_no_types.mk_lstring l None c (Some ty)))



(* num patterns *)
let mk_opt_let_exp l (n, e1) e2 = 
begin
  let vs = nfmap_domain (C_no_types.exp_to_free e2) in
  if NameSet.mem n vs then (true, (mk_paren_exp (mk_let_exp l (n, e1) e2))) else (false, e2)
end

let num_add_matrix_compile_fun (gen_match : bool) (use_split : int -> bool) env (gen : var_name_generator) (m_ty : Types.t) l_org : matrix_compile_fun = fun pL ->
  let _ = matrix_compile_fun_check (List.exists (fun p -> is_num_add_pat p) pL) in 
  let _ = matrix_compile_fun_check (List.for_all (fun p -> ((is_num_add_pat p || is_num_pat p || is_wild_pat p))) pL) in
  let loc = Ast.Trans (true, "num_add_matrix_compile_fun", Some l_org) in
  let num_ty = annot_to_typ (List.hd pL) in

  (* find the smallest add-number (except 0) we need to be able to handle, then perform the split:
     0, 1, 2, ..., min - 1, x + min *)
  let (min_inc, min_name_opt) = List.fold_left (fun (min, no) p -> match dest_num_add_pat p with None -> (min, no) | Some (n, i) -> if min = 0 || i < min then (i, Some n) else (min, no)) (0, None) pL in

  let below_min_inc_missing = begin
    let constL = List.fold_left (fun acc p -> match dest_num_pat p with None -> acc |  Some i -> if (i < min_inc) then i :: acc else acc) [] pL in
    min_inc - (List.length (Util.remove_duplicates constL))
  end in

  let cL = let rec aux b = function 0 -> [] | n -> b :: aux (b + 1) (n - 1) in aux 0 min_inc in

  (* Build top-fun *)
  let top_fun_if : matrix_compile_top_fun  = fun i eL -> 
     let _ = matrix_compile_fun_check (List.length eL = (min_inc + 1)) in
     let rec aux cL eL = match (cL, eL) with 
         ([], [e]) -> e
       | (c::cs, e::es) ->                        
          let c_exp = mk_num_exp num_ty c in
          let eq_exp = mk_eq_exp env i c_exp in
          mk_if_exp loc eq_exp e (aux cs es)
       | _ -> raise Pat_Matrix_Compile_Fun_Failed (* Should not happen *)
     in aux cL eL
  in
  let top_fun_case last_used last_n : matrix_compile_top_fun  = fun i eL -> 
     let _ = matrix_compile_fun_check (List.length eL = (min_inc + 1)) in
     let pL = (List.map (mk_num_pat num_ty) cL) @ [if last_used then matrix_compile_mk_pvar last_n num_ty else matrix_compile_mk_pwild num_ty] in
     mk_case_exp true loc i (List.combine pL eL) m_ty
  in
  let abb_n = gen min_name_opt num_ty in
  let abb_v = matrix_compile_mk_var abb_n num_ty in
  let top_fun_split (i : exp) (eL : exp list) = begin
    let (eL0, eL1) = Util.split_after (List.length eL - 1) eL in
    let (i', _) = alter_init_lskips remove_init_ws i in

    let real_gen_match = gen_match && List.length eL > 2 in
    let last_n = gen None num_ty in
    let last_e = if real_gen_match then matrix_compile_mk_var last_n num_ty else i' in

    let e_last : exp = List.hd eL1 in
    let (last_used, e_last') = mk_opt_let_exp loc (abb_n, mk_sub_exp env last_e (mk_num_exp num_ty min_inc)) e_last in
    let eL' = eL0 @ [e_last'] in

    let res = if real_gen_match then top_fun_case last_used last_n i' eL' else top_fun_if i' eL' in
    res
  end in

  let top_fun_ge (i : exp) (eL : exp list) = 
  match eL with [e1;e2] ->
  begin
    let (_, e1') = mk_opt_let_exp loc (abb_n, mk_sub_exp env i (mk_num_exp num_ty min_inc)) e1 in
    let (i', _) = alter_init_lskips remove_init_ws i in
    let le_exp = mk_le_exp env (mk_num_exp num_ty min_inc) i' in
    mk_if_exp loc le_exp e1' e2
  end | _ -> assert false in


  let restr_pat_eq i _ = mk_num_pat num_ty i in
  let restr_pat_ge i = function 
      [p] -> num_ty_pat_cases (fun n -> mk_num_add_pat num_ty n i) (fun i' -> mk_num_pat num_ty (i+i')) (fun n i' -> mk_num_add_pat num_ty n (i+i')) p
                 (fun p -> raise (match_compile_unreachable "expression was no number expression")) p
    | _ -> raise (match_compile_unreachable "list_matrix_compile_fun wrong no of args to rest_pat_ge")
  in
  let restr_pat_less = function 
      [p] -> p
    | _ -> raise (match_compile_unreachable "list_matrix_compile_fun wrong no of args to rest_pat_le")
  in

  let new_w = matrix_compile_mk_pwild num_ty in

  let pat_cases f_i f_a f_w p =
      Util.option_cases (dest_num_pat p) f_i (fun () ->
        Util.option_cases (dest_num_add_pat p) (fun (n,i) -> f_a n i)
           (fun () -> if is_wild_pat p then f_w else raise (match_compile_unreachable "Unexpected pattern in num_add_matrix_compile_fun"))) in

  let case_fun_eq i p ee = 
     pat_cases (fun i' -> if i' = i then Some ([], ee) else None)  
               (fun n i' -> if i' <= i then Some ([], add_to_ext_exp ee n (mk_num_exp num_ty (i - i'))) else None)
               (Some ([], ee)) p in

  let case_fun_ge i p ee = 
    pat_cases (fun i' -> (if i' < i then None else Some ([mk_num_pat num_ty (i'-i)], ee)))
              (fun n i' -> if i' < i then raise (match_compile_unreachable "because we choose the smallest i") else Some ([mk_num_add_pat num_ty n (i'-i)], ee)) 
              (Some ([new_w], ee)) p in

  let case_fun_less i p ee = 
    pat_cases (fun i' -> (if i' < i then Some ([p], ee) else None))
              (fun n i' -> (if i' < i then Some ([p], ee) else None))
              (Some ([new_w], ee)) p in

  let dest_in_eq e = [] in
  let dest_in_ge e = [abb_v] in
  let dest_in_less e = [e] in

  let res_split = (top_fun_split, (List.map (fun i -> (case_fun_eq i, dest_in_eq, restr_pat_eq i)) cL) @ [(case_fun_ge min_inc, dest_in_ge, restr_pat_ge min_inc)], fun e -> None) in
  let res_ge = (top_fun_ge, [(case_fun_ge min_inc, dest_in_ge, restr_pat_ge min_inc); (case_fun_less min_inc, dest_in_less, restr_pat_less)], fun e -> None) in
  if (use_split below_min_inc_missing) then Some res_split else Some res_ge


(******************************************************************************)
(* Check for properties of check                                              *)
(******************************************************************************)

type match_props_aux = {mis_pats: (pat list) list; redundant_rows: Util.IntSet.t; overlapping_rows : Util.IntIntSet.t};;
type match_props = {is_exhaustive: bool; missing_pats : (pat list) list; redundant_pats: (int * pat) list; overlapping_pats : ((int * pat) * (int * pat)) list };;

module IntSetE = Util.ExtraSet (Util.IntSet)
module IntIntSetE = Util.ExtraSet (Util.IntIntSet)
module NameSetE = Util.ExtraSet(NameSet)

let rec pat_matrix_check_aux l_org (cf : matrix_compile_fun) (m : pat_matrix) : match_props_aux =
  (* simplify matrix *)
  let m_simp = pat_matrix_simps l_org m in

  if (is_empty_pat_matrix m_simp) then
     {mis_pats = [pat_matrix_to_pat m_simp]; 
      redundant_rows = Util.IntSet.empty; overlapping_rows = Util.IntIntSet.empty}
  else if (is_trivial_pat_matrix m_simp) then
    let (no_first, no_L) = match m_simp with 
        (_, [], _) -> raise (match_compile_unreachable "trivial matrix was empty")
      | (_, ((no, _, _) :: rL), _) -> (no, List.map (fun (n, _, _) -> n) rL) in
     {mis_pats = []; 
      redundant_rows = IntSetE.from_list no_L; 
      overlapping_rows = IntIntSetE.from_list (List.map (fun n -> (no_first, n)) no_L)}
  else begin
    let col_no = pat_matrix_compile_find_col m_simp in
    let (top_fun, mL) = pat_matrix_compile_step cf col_no m_simp in

    let mpL = List.map (fun (rL, m) ->
      let mp: match_props_aux = pat_matrix_check_aux l_org cf m in
      let rs = IntSetE.add_list mp.redundant_rows rL in
      {mp with redundant_rows = rs}) mL in

     {mis_pats = List.flatten (List.map (fun mp -> mp.mis_pats) mpL); 
      redundant_rows = IntSetE.list_inter (List.map (fun mp -> mp.redundant_rows) mpL); 
      overlapping_rows = IntIntSetE.list_union (List.map (fun mp -> mp.overlapping_rows) mpL)}
  end

let pat_matrix_check l_org (cf : matrix_compile_fun) (m : pat_matrix) : match_props =
  let mp = pat_matrix_check_aux l_org cf m in
  let get_pat n = match m with (_, rows, _) -> (n, match (List.nth rows n) with (_, pL, _) -> List.hd pL) in
  let red_pats = begin
    let rowL = Util.IntSet.elements mp.redundant_rows in
    let argL = List.map get_pat rowL in
    argL
  end in
  let over_pats = begin
    let pairL = Util.IntIntSet.elements mp.overlapping_rows in
    let overL = List.map (fun (i,j) -> (get_pat i, get_pat j)) pairL in
    overL
  end in
  {is_exhaustive = (mp.mis_pats = []); missing_pats = mp.mis_pats; redundant_pats = red_pats; overlapping_pats = over_pats} 


(******************************************************************************)
(* Compilation functions which are used                                       *)
(******************************************************************************)

(* [basic_compile_funs] are used for checking for reduncy, missing patterns and
   as a fallback when no target specific function fires. *)


let basic_compile_funs (targ : Target.target) : (bool -> env -> var_name_generator -> Types.t -> Ast.l -> matrix_compile_fun) list = 
   [(fun _   -> tuple_matrix_compile_fun); 
    (fun _ _ -> bool_matrix_compile_fun false); 
    (fun _   -> list_matrix_compile_fun); 
    (           constr_matrix_compile_fun targ);    
    (fun _   -> num_matrix_compile_fun true);   
    (fun _   -> num_add_matrix_compile_fun true (fun _ -> true)); 
    (fun _   -> string_matrix_compile_fun false); 
    (fun _   -> record_matrix_compile_fun)]

(* Target specific ones, use [basic_compile_funs] as a fallback. *)
let get_target_compile_funs (topt:target) : (bool -> env -> var_name_generator -> Types.t -> Ast.l -> matrix_compile_fun) list =  begin
  let rec target_compile_funs topt =
    match topt with
    | Target_no_ident Target_ocaml -> [
         (fun _   -> num_add_matrix_compile_fun false (fun i -> i < 3)); (* if less than 3 cases are missing list all cases, otherwise use >= *)
         (fun _   -> num_matrix_compile_fun false);   
      ]
    | Target_no_ident Target_hol -> [
         (fun _ _ -> bool_matrix_compile_fun true); 
         (fun _   -> string_matrix_compile_fun true); 
         (fun _   -> num_matrix_compile_fun false);   
         (fun _   -> num_add_matrix_compile_fun true (fun i -> i < 3)); 
      ]
    | Target_no_ident Target_isa -> [
         (fun _   -> num_matrix_compile_fun false);   
         (fun _   -> num_add_matrix_compile_fun true (fun i -> i < 3)); 
      ]
    | Target_no_ident Target_coq -> [
         (fun _   -> num_matrix_compile_fun false);   
         (fun _   -> num_add_matrix_compile_fun true (fun i -> i < 3)); 
      ]
    | Target_ident -> (* make identity behave like ocaml for debug, controlled by flag !ident_force_pattern_compile *) target_compile_funs (Target_no_ident Target_ocaml) 
    | _ -> []
  in target_compile_funs topt @ basic_compile_funs topt
end

(******************************************************************************)
(* Check properties of matches                                                *)
(******************************************************************************)

let check_match_internal l env ws m = 
  let cfL = List.map (fun cf -> cf false env) (basic_compile_funs Target_ident) in
  let gen = mk_var_name_gen (pat_matrix_vars m) in
  let ty = pat_matrix_to_typ m in
  let cf = combine_matrix_compile_fun l gen ty cfL in
  try
     let mp = pat_matrix_check l cf m in Some mp
  with Pat_Matrix_Compile_Failed pL -> 
        (Reporting.report_warning env (Reporting.Warn_pattern_compilation_failed (l, pL, ws)); None)

let check_match_exp env e =
  let l = exp_to_locn e in 
  match exp_to_pat_matrix e with 
      None -> None
    | Some m -> check_match_internal l env (Reporting.Warn_source_exp e) m 

let check_pat_list env pL =
  let l = Ast.Trans (true, "check_pat_list", None) in 
  match pat_list_to_pat_matrix pL with 
      None -> None 
    | Some m -> check_match_internal l env Reporting.Warn_source_unkown m 

let pat_matrix_unused_vars_warn env ws ((_, rows, _) : pat_matrix) : unit =
  let row_check ((_, pL, ee):pat_matrix_row) = begin
    let used = pat_matrix_ext_exp_vars ee in
    let check_pat p = let p_vars = nfmap_domain p.rest.pvars in
                      let unused = NameSet.diff p_vars used in
                      let unusedL = List.map Name.to_string (NameSet.elements unused) in
                      unusedL in
    List.flatten (List.map check_pat pL)
  end in
  let unusedL = List.flatten (List.map row_check rows) in
  (* ignore variables starting with underscore, like in OCaml *)
  let unusedL' = List.filter (fun s -> s.[0] <> '_') unusedL in
  if unusedL' = [] then () else Reporting.report_warning env (Reporting.Warn_unused_vars (Reporting.warn_source_to_locn ws, unusedL', ws))


let check_match_exp_warn env e = 
  let l = exp_to_locn e in 
  let check = match exp_to_pat_matrix e with 
      None -> None 
    | Some m -> Util.option_map (fun mp -> (m, mp)) (check_match_internal l env (Reporting.Warn_source_exp e) m) in
  match check with
      None -> ()
    | Some (m, mp) -> 
        let _ = if mp.is_exhaustive then () else Reporting.report_warning env (Reporting.Warn_pattern_not_exhaustive (l, mp.missing_pats)) in
        let _ = if (mp.redundant_pats = []) then () else (Reporting.report_warning env (Reporting.Warn_pattern_redundant (l, mp.redundant_pats, e))) in
        let _ = pat_matrix_unused_vars_warn env (Reporting.Warn_source_exp e) m in
        ()

let check_match_def env d =
  let mL = def_to_pat_matrix_list d in
  let check_matrix (n, (_,m), l) = Util.option_map (fun mp -> (n, mp)) (check_match_internal l env (Reporting.Warn_source_def d) m) in
  Util.map_filter check_matrix mL

let check_match_def_warn env d =
  let match_props_to_warnings_def n l mp =
    let _ = if mp.is_exhaustive then () else Reporting.report_warning env (Reporting.Warn_def_not_exhaustive (l, Name.to_string n, mp.missing_pats)) in
    let _ = if (mp.redundant_pats = []) then () else (Reporting.report_warning env (Reporting.Warn_def_redundant (l, Name.to_string n, mp.redundant_pats, d))) in
    ()
  in
  let mL = def_to_pat_matrix_list d in   
  let warn_matrix (n, (c, m), l) =     
    let _ = Util.option_map (match_props_to_warnings_def n l) (check_match_internal l env (Reporting.Warn_source_def d) m) in
    let _ = if not c then pat_matrix_unused_vars_warn env (Reporting.Warn_source_def d) m else () in
    () in
  let _ = List.map warn_matrix mL in
  ()
  

(******************************************************************************)
(* Match check arguments                                                      *)
(******************************************************************************)

(* match_check_arg contains 
     exp_OK : is a given expression in a given environment supported (except match-expressions)?
     def_OK : is a given definition in a given environment supported?

     match-expressions are judged using the follwoing 3 parameters, all other expressions using exp_OK

     pat_OK               : is a given pattern as part of a case (match) statement supported?
     allow_non_exhaustive : are non-exhaustive pattern matches allowed?
     allow_redundant      : are redundant pattern matches allowed?

     a match is excepted, if it is exhaustive or (non-exhaustive is allowed), contains
     no redundant patterns (or redundant patterns are allowed) and all patterns in the
     match satisfy pat_OK
*)

type match_check_arg = {
  exp_OK: (env -> exp -> bool); 
  def_OK: (env -> def -> bool); 
  allow_non_exhaustive : bool;
  allow_redundant : bool;
  pat_OK: (env -> pat -> bool)}

let match_check_arg_match_OK env mca e = 
  let l = exp_to_locn e in 
  match exp_to_pat_matrix e with 
      None -> false 
    | Some m -> begin
      List.for_all (mca.pat_OK env) (pat_matrix_pats m) &&
      (match check_match_internal l env (Reporting.Warn_source_exp e) m with None -> true 
        | Some mp -> (mp.is_exhaustive || mca.allow_non_exhaustive) &&
                     (mp.redundant_pats = [] || mca.allow_redundant))
     end

(******************************************************************************)
(* Collapse patterns                                                          *)
(******************************************************************************)

(* collapse_nested_matches_dest_pat_fun determines how the new patterns should look like,
   when collapsing nested pattern matches.
   For example, given an expression 

   match i with (x1, ..., xn) -> match e with p1 -> e1 | ... | pm -> em

   it is given the pattern "(x1, ..., xn)" (as argument "ps"), the expression e (as arg "es"). It then 
   tries to find a destruction function "d" such that the original definition is equivalent to

   match i with 
       | (d p1) = e1
       | (d p2) = e2
       ...
       | (d pm) = em

   for technical reasons e and p are not given directly, but in the form of lists. This makes
   destruction of tuples easier. Moreover, the function gets the set of all free variables in the match,
   i.e. the parameter names that are not allowed to be substituted.
*)   

let rec collapse_nested_matches_dest_pat_fun l env (no_replace_set : NameSet.t) (ps : pat list) (es : exp list) : ((pat list -> (pat list option)) option) =
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  match Util.list_index (fun e -> not (Typed_ast_syntax.is_var_exp e)) es with None ->
  begin
    (* simple case of only variable exporessions in es *)
    match Util.list_index (fun p -> not (Pattern_syntax.is_var_pat p)) ps with None ->
    begin
      (* the most basic case where all expressions and patterns are variables. So, one "only" needs to do matching *)
      let es_n = List.map (fun e -> match dest_var_exp e with Some n -> n | None -> raise (Reporting_basic.err_unreachable Ast.Unknown "Not reachable, because of check")) es in
      let get_pat_fun (p : pat) : (pat list -> pat option) = begin 
        match Pattern_syntax.dest_var_pat p with None -> raise (Reporting_basic.err_unreachable Ast.Unknown "Not reachable, because of check") | Some n -> (
        match (Util.list_index (fun n' -> Name.compare n n' = 0) es_n) with
          None -> (* variable does not occur, so let's keep the old one *) (fun _ -> Some p)
        | Some i -> 
            (if NameSet.mem n no_replace_set then (fun _ -> None) else 
               (fun pL -> try 
                 let p = List.nth pL i in
                 let (p', _) = pat_alter_init_lskips remove_init_ws p in
                 let p'' = Pattern_syntax.mk_opt_paren_pat p' in 
                 Some p'' 
               with Failure _ -> None)))
      end in
      let pat_funL = List.map get_pat_fun ps in
      let res pL = Util.map_all (fun sL -> sL pL) pat_funL in
      Some res
    end | Some p_i -> 
    begin 
      (* at position p_i there is a non-variable pattern, try to destruct it *)
      let p = List.nth ps p_i in
      let p_ty = (annot_to_typ p) in
      let l' = Ast.Trans (true, "remove_toplevel_match_dest_pat_fun", Some l) in
      let skip_res = ([], (fun _ -> p), NameSet.elements (nfmap_domain p.rest.pvars)) in
      let ((pL, d_f, new_avoid) : (pat list *  (pat list -> pat) * Name.t list)) = match p.term with
        | P_as (s1,p,s2,(n,l),s3) -> ([], (fun pL -> C.mk_pas l s1 (List.hd pL) s2 (n, l) s3 (Some p_ty)), [Name.strip_lskip n])
        | P_typ (s1,p,s2,src_t,s3) -> ([p], (fun pL -> C.mk_ptyp l s1 (List.hd pL) s2 src_t s3 (Some p_ty)), [])
        | P_const (id, pL) -> (pL, (fun pL' -> C.mk_pconst l id pL' (Some p_ty)), [])
        | P_backend (sk, i, ty, pL) -> (pL, (fun pL' -> C.mk_pbackend l sk i ty pL' (Some p_ty)), [])
        | P_tup (s1,ps,s2) -> (Seplist.to_list ps, (fun pL -> C.mk_ptup l' s1 (Seplist.from_list_default None pL) s2 (Some p_ty)), [])
        | P_list (s1,ps,s2) -> (Seplist.to_list ps, (fun pL -> C.mk_plist l' s1 (Seplist.from_list_default None pL) s2 p_ty), [])
        | P_paren (s1, p, s2) -> ([p], (fun pL -> C.mk_pparen l s1 (List.hd pL) s2 (Some p_ty)), [])
        | P_cons (p1, s, p2) -> ([p1; p2], (function | [p1'; p2'] -> C.mk_pcons l p1' s p2' (Some p_ty) 
                                                     | _ -> raise (Failure "")), [])
        | P_var_annot _ -> ([split_var_annot_pat p], List.hd, []) 
        | P_num_add _ -> skip_res (*TODO*)
        | P_record _ -> skip_res (*TODO*)
        | P_vector _ -> skip_res (*TODO*)
        | P_vectorC _ -> skip_res (*TODO*)

        | P_var _ -> skip_res (* should not happen *)
        | P_wild _ -> skip_res
        | P_lit _ -> skip_res in
      begin
	let (ps', ps''0) = Util.split_after p_i ps in
        let ps'' = List.tl ps''0 in
        let no_replace_set' = List.fold_left (fun s n -> NameSet.add n s) no_replace_set new_avoid in
        let res_opt = collapse_nested_matches_dest_pat_fun l env no_replace_set' (ps' @ pL @ ps'') es in
        let res_fun ps_res = try
          let (ps', ps''0) = Util.split_after p_i ps_res in
          let (ps'', ps''') = Util.split_after (List.length pL) ps''0 in
          Some (ps' @ ((d_f ps'') :: ps''')) 
        with Failure _ -> None in
        Util.option_map (fun d pL -> Util.option_bind res_fun (d pL)) res_opt
      end
    end
  end | Some e_i -> 
  begin
    (* at position e_i there is a non_variable expression, 
       handle tuples, but nothing more fancy. *)
    let e = strip_paren_typ_exp (List.nth es e_i) in
    match dest_tup_exp None e with 
      | None -> None
      | Some eL -> begin
	let (es', es''0) = Util.split_after e_i es in
        let es'' = List.tl es''0 in
        let res_opt = collapse_nested_matches_dest_pat_fun l env no_replace_set ps (es' @ eL @ es'') in
        let res_fun d ps_arg = try 
          let (ps', ps''0) = Util.split_after e_i ps_arg in
          let (p, ps'') = (List.hd ps''0, List.tl ps''0) in
          let pL = match dest_tup_pat (Some (List.length eL)) p with None -> raise (Failure "") | Some pL -> pL in
          d  (ps' @ pL @ ps'')
        with Failure _ -> None in
        Util.option_map res_fun res_opt
      end
  end


let rec collapse_nested_matches mca env exp =
  let l_unk = Ast.Trans (true, "collapse_nested_matches", Some (exp_to_locn exp)) in
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  match C.exp_to_term exp with 
    | Case (ec, es1, ee, es2, epats, es3) -> 
      begin
        let process_row (((p_row, s_row, e_row, l_row) : (pat * lskips * exp * Ast.l)), se_row) :  ((pat * lskips * exp * Ast.l) * lskips) list option = begin 
           let e_row' = strip_paren_typ_exp e_row in
           match (check_match_exp env e_row', C.exp_to_term e_row') with 
             | (Some mp, Case (nc, ns1, ne, ns2, npats, ns3)) -> 
               if not (mp.is_exhaustive) then None else 
               begin
                 let free_vars_row s (p, _, e, _) = NameSet.union s (NameSet.diff (nfmap_domain (C.exp_to_free e)) (nfmap_domain p.rest.pvars)) in
                 let free = List.fold_left free_vars_row NameSet.empty (Seplist.to_list npats) in
                 let dest_f_opt = collapse_nested_matches_dest_pat_fun l_unk env free [p_row] [ne] in
                 match dest_f_opt with None -> None | Some dest_f ->
                 begin
                   let adapt_ws_p p = (let (p', _) = pat_alter_init_lskips space_com_init_ws p in p') in
                   let work_row (p, _, e, l) =
                      Util.option_map (fun pL -> ((adapt_ws_p (List.hd pL), s_row, e, l), se_row)) (dest_f [p]) in                 
                   Util.map_all work_row (Seplist.to_list npats)
                 end
               end
             | _ -> None
        end in
        let patexpsL : ((pat * lskips * exp * Ast.l) * lskips) list = snd (Seplist.to_pair_list None epats) in
        let patexpsL'_opt : ((pat * lskips * exp * Ast.l) * lskips) list list option = Util.map_changed_default (fun x -> [x]) process_row patexpsL in
        match patexpsL'_opt with None -> None | Some patexpsL' -> (
          let patexps' = Seplist.from_list (List.flatten patexpsL') in
          let new_exp0 =  C.mk_case ec l_unk es1 ee es2 patexps' es3 (Some (exp_to_typ exp)) in
          let new_exp = Util.option_default new_exp0 (collapse_nested_matches mca env new_exp0) in
          if match_check_arg_match_OK env mca new_exp then Some new_exp else None)
      end
    | _ -> None

         
(*

  let aux sk1 sk2 topt sl tnvs class_constraints = begin
    let (_, sk_first_opt, group_nameL) = funcl_aux_seplist_group sl in
    let groupL = List.map (fun (_, x) -> x) group_nameL in
    let group_apply sl = if not (Seplist.length sl = 1) then None else   
    match Seplist.to_list sl with 
      | ([] | _ :: _ :: _) -> raise (Reporting_basic.err_unreachable true l_unk "Not reachable, because of length check")
      | [(n,ps,topt,s,e)] -> 
          let e0 = strip_paren_typ_exp e in
          let e1 = Util.option_default e0 (compile_match_exp targ mca env e0) in
          let e2 = strip_paren_typ_exp e1 in
          (match C.exp_to_term e2 with Case(_,s1,e',s2,pats,s3) -> (       
          let free_vars_row s (p, _, ee, _) = NameSet.union s (NameSet.diff (nfmap_domain (C.exp_to_free ee)) (nfmap_domain p.rest.pvars)) in
          let free = List.fold_left free_vars_row NameSet.empty (Seplist.to_list pats) in
          match collapse_nested_matches_dest_pat_fun l_unk free ps [e'] with None -> None | Some dest_f ->
          begin 
            let adapt_ws_pL pL = List.map (fun p -> let (p', _) = pat_alter_init_lskips space_com_init_ws p in p') pL in
            let work_row ((p, _, ee, _) : (pat * lskips * exp * Ast.l)) : funcl_aux option =
              Util.option_map (fun pL -> (n, adapt_ws_pL pL, topt, s, ee)) (dest_f [p]) in
            let sl_opt = Util.map_all (fun r -> Util.option_map (fun x -> (x, new_line)) (work_row r)) (Seplist.to_list pats) in
            Util.option_map Seplist.from_list sl_opt
          end)
          | _ -> None) in
    match (Util.map_changed group_apply groupL) with None -> None | Some sll' ->
      let sl' = Seplist.flatten space sll' in
      let new_d = ((Val_def ((Rec_def (sk1, sk2, topt, sl')), tnvs, class_constraints), s), l) in
      if mca.def_OK env new_d then Some (env_local, [new_d]) else None
  end in
  match d with 
  |  Val_def ((Let_def (sk1, topt, (Let_fun funcl_aux, _))), tnvs, class_constraints) -> 
       aux sk1 None topt (Seplist.from_list [(funcl_aux, None)]) tnvs class_constraints
  |  Val_def ((Rec_def (sk1, sk2, topt, sl)), tnvs, class_constraints) -> begin 
       aux sk1 sk2 topt sl tnvs class_constraints
     end
  | _ -> None

*)


(******************************************************************************)
(* Do the compilation for matches                                             *)
(******************************************************************************)

let is_supported_pat_matrix loc mca env m = 
  (List.for_all (mca.pat_OK env) (pat_matrix_pats m)) (* check not necessary thanks to following cleanup &&  
    (match check_match_exp env (pat_matrix_to_exp loc env m) with None -> false | Some mp -> begin
    (List.for_all (mca.pat_OK env) (List.flatten mp.missing_pats)) &&
    (mp.is_exhaustive || mca.allow_non_exhaustive) &&
    (mp.redundant_pats = [] || mca.allow_redundant)
  end)*)

let cleanup_match_exp env add_missing e = 
  let l = exp_to_locn e in 
  let loc = Ast.Trans (true, "cleanup_match_exp", Some l) in
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  match C.exp_to_term e with 
    Case(_,s1,e',s2,patexps,s3) -> 
    (match check_match_exp env e with None -> None | Some mp -> 
    if (mp.is_exhaustive && mp.redundant_pats = []) then None else
    begin
      let (first_s_opt, rowL) = Seplist.to_pair_list None patexps in
      let middle_s = match rowL with 
        | [] -> raise (Reporting_basic.err_unreachable loc "cleanup_match_exp rowL empty")
        | (_ :: (_, s) :: _) -> s 
	| [(_, s)] -> s in
      let last_s = match List.rev rowL with
        | [] -> raise (Reporting_basic.err_unreachable loc "cleanup_match_exp rowL empty")
	| (_, s) :: _ -> s in      
      let fix_last_s rowL last_s = match List.rev rowL with
        | [] -> raise (Reporting_basic.err_unreachable loc "cleanup_match_exp rowL empty")
	| (x, s) :: xss -> List.rev ((x, last_s) :: xss) in

      (* remove redundant rows *)
      let (_, rowL') = List.fold_left (fun (i, res) row ->
            if (List.exists (fun (i', _) -> i' = i) mp.redundant_pats) then
               (i+1, res) else (i+1, row::res))
            (0, []) rowL in
      let rowL' = List.rev rowL' in

      (* add missing patterns *)
      let undef_exp = begin
        let mes = "Incomplete Pattern at " ^ String.escaped (Reporting_basic.loc_to_string true l) in
        mk_undefined_exp l mes (exp_to_typ e) 
      end in
      let mis_rows = List.map (fun pL -> ((pat_append_lskips space (List.hd pL), space, undef_exp, loc), middle_s)) mp.missing_pats in
      let rowL'' = if add_missing then ((fix_last_s rowL' middle_s) @ mis_rows) else rowL' in

      (* build the case statement again *)
      let patexps' = Seplist.from_list (fix_last_s rowL'' last_s) in
      let patexps'' = match first_s_opt with None -> patexps' | Some s -> Seplist.cons_sep s patexps' in
      let res = C.mk_case true loc s1 e' s2 patexps'' s3 (Some (exp_to_typ e)) in
      Some res
    end)
  | _ -> None


let rec pat_matrix_compile (l : Ast.l) mca env (undef_exp : exp) (cf : matrix_compile_fun) (m : pat_matrix) : exp =
  (* simplify matrix *)
  let m_simp = pat_matrix_simps l m in
  if (is_empty_pat_matrix m_simp) then
     undef_exp
  else if (is_trivial_pat_matrix m_simp) then
     trivial_pat_matrix_to_exp m_simp
  else if (is_supported_pat_matrix l mca env m_simp) then
     let res = pat_matrix_to_exp l env m_simp in
     Util.option_default res (cleanup_match_exp env (not mca.allow_non_exhaustive) res)
  else begin
    let col_no = pat_matrix_compile_find_col m_simp in
    let (top_fun, mL) = pat_matrix_compile_step cf col_no m_simp in
    let eL = List.map (fun (_, m) -> pat_matrix_compile l mca env undef_exp cf m) mL in
    top_fun eL
  end

let compile_match_exp topt mca env e = 
  let cfL = List.map (fun cf -> cf true env) (get_target_compile_funs topt) in
  let loc = exp_to_locn e in
  match case_exp_to_pat_matrix true e with
      None -> None
    | Some m ->  
      match check_match_internal loc env (Reporting.Warn_source_exp e) m with None -> None | Some mp ->
      if (List.for_all (mca.pat_OK env) (List.flatten mp.missing_pats @ (pat_matrix_pats m))) then (
         (* No full compilation is necessary. Check whether missing patterns need adding / redunant removing *)
         if (mp.is_exhaustive || mca.allow_non_exhaustive) &&
            (mp.redundant_pats = [] || mca.allow_redundant) then None else
         cleanup_match_exp env (not mca.allow_non_exhaustive) e
      ) else try        
        let gen = mk_var_name_gen (pat_matrix_vars m) in
        let matrix_ty = exp_to_typ e in
        let cf = combine_matrix_compile_fun loc gen matrix_ty cfL in

        let undef_exp = begin
          let mes = "Incomplete Pattern at " ^ String.escaped (Reporting_basic.loc_to_string true loc) in
          let loc' = Ast.Trans (true, "pat_matrix_compile", Some loc) in
          mk_undefined_exp loc' mes matrix_ty 
        end in
        let e' = pat_matrix_compile loc mca env undef_exp cf m in
        let e'' = Util.option_default e' (collapse_nested_matches mca env e') in
        let com = lskips_only_comments [case_exp_extract_lskips e] in
        let e''' = append_lskips com e'' in
        let _ = Reporting.report_warning env (Reporting.Warn_pattern_needs_compilation (loc, topt, e, e'')) in
        Some e'''
      with Pat_Matrix_Compile_Failed pL -> 
           (Reporting.report_warning env (Reporting.Warn_pattern_compilation_failed (loc, pL, Reporting.Warn_source_exp e)); None)


(******************************************************************************)
(* Compilation for arbitrary expressions and definitions                      *)
(******************************************************************************)

(* Pattern compilation essentially works on match (case) expressions. Such expressions
   can be compiled via "compile_match_exp". In order to compile patterns occuring
   in function / fun / let etc expressions as well as patterns in definitions, they 
   are compiled to match expressions first. *)

(* Turn function | pat1 -> exp1 ... | patn -> expn end into
 * fun x -> match x with | pat1 -> exp1 ... | patn -> expn end *)
let remove_function env (comp: exp -> exp) e = 
    let l_unk = Ast.Trans(true, "remove_function", Some (exp_to_locn e)) in
    let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
      match C.exp_to_term e with
        | Function(s1,cases,s2) ->
            let free = C.exp_to_free e in
            let v = Name.fresh (r"x") (fun n -> not (Nfmap.in_dom n free)) in
            let (from_t,to_t) =
              match (Types.head_norm env.t_env (exp_to_typ e)).Types.t with
                | Types.Tfn(t1,t2) -> (t1,t2)
                | _ -> assert false
            in
            let pat_v = C.mk_pvar l_unk (Name.add_lskip v) from_t in
            let exp_v = C.mk_var l_unk (Name.add_lskip v) from_t in
            let case_exp =  C.mk_case false l_unk space exp_v space cases s2 (Some to_t) in
            let case_exp' = comp case_exp in
               Some(C.mk_fun l_unk s1 [pat_v] space case_exp' (Some (exp_to_typ e)))
        | _ -> None


(* Remove patterns from (fun ps -> ...), except for variable and wildcard patterns *)
let remove_fun env (comp: exp -> exp) e = 
  let loc = Ast.Trans(true, "remove_fun", Some (exp_to_locn e)) in
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  match C.exp_to_term e with
    | Fun(s1,ps,s2,e') -> if (List.for_all is_ext_var_pat ps) then None else
        let gen = mk_var_name_gen (nfmap_domain (C.exp_to_free e')) in
        let get_p_info p = (let ty = annot_to_typ p in let n = pattern_gen gen p in (n, ty)) in
        let p_info = List.map get_p_info ps in

        let (vars_t, pats_t) = begin
          let var_seplist = (Seplist.from_list (List.map (fun (n, ty) -> (matrix_compile_mk_var n ty, space)) p_info)) in
          let pats_seplist = (Seplist.from_list (List.map (fun p -> (p, space)) ps)) in
          let tup_ty = { Types.t = Types.Ttup (List.map (fun (_, ty) -> ty) p_info) } in
          let vars_t = C.mk_tup loc space var_seplist space (Some tup_ty) in
          let pats_t = C.mk_ptup loc space pats_seplist space (Some tup_ty) in
          (vars_t, pats_t)
        end in

        let cases = Seplist.from_list [((pat_append_lskips space pats_t, space, e', loc), space)] in
        let case_exp =  C.mk_case false loc space vars_t space cases space (Some (exp_to_typ e')) in

        let psvar = List.map (fun (n, ty) -> matrix_compile_mk_pvar n ty) p_info in
        Some(C.mk_fun loc s1 psvar s2 (comp case_exp) (Some (exp_to_typ e)))
      | _ -> None
;;

let remove_let env (comp: exp -> exp) e = 
  let loc = Ast.Trans(true, "remove_let", Some (exp_to_locn e)) in
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  match C.exp_to_term e with
    | Let(s1,(Let_fun(n, ps, topt, s2, e1),l),s3,e2) ->
         let fun_t = List.fold_right (fun p t -> { Types.t = Types.Tfn (p.typ, t) }) ps (exp_to_typ e1) in
         let fun_exp = C.mk_fun loc space ps s2 e1 (Some fun_t) in
         let fun_exp' = Util.option_default fun_exp (remove_fun env comp fun_exp) in
         let let_val = (C.mk_let_val loc (C.mk_pvar loc n.term n.typ) None space (mk_opt_paren_exp fun_exp')) in
         let let_exp = C.mk_let loc s1 let_val s3 e2 (Some (exp_to_typ e2)) in
           Some let_exp
    | Let(s1,(Let_val(p,topt,s,e'),l),s2,e) -> if (is_var_wild_pat p) then None else
         let cases = Seplist.from_list [((pat_append_lskips space p, s, e, loc), space)] in
         let case_exp =  C.mk_case false loc s1 e' space cases s2 (Some (exp_to_typ e)) in
            Some (comp case_exp)
    | _ -> None


(* Removes patterns from restricted quantification.
 * forall (p IN e). P x  goes to
 * forall x IN e. match x with p --> P x | _ -> true*)

let remove_fun_restr_quant_aux_gen qbs eL =
  begin
       let vs0 = List.fold_left NameSet.union NameSet.empty (List.map (fun e -> (nfmap_domain (C_no_types.exp_to_free e))) eL) in
       let vars = List.fold_left (fun s -> function Qb_var n ->  NameSet.add (Name.strip_lskip (n.term)) s
                                                  | Qb_restr (_, _, p, _, _, _) -> NameSet.union s (nfmap_domain p.rest.pvars))
                      vs0 qbs in
       let gen = mk_var_name_gen vars in gen
  end

let remove_pat_restr_quant_aux loc env qbs is_forall e eL =
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
   let gen = remove_fun_restr_quant_aux_gen qbs (e::eL) in
   let (new_qbs, ml) =
      List.fold_right 
         (fun qb (qbs, ml) ->
            match qb with
              | Qb_var(n) -> (qb::qbs, ml)
              | Qb_restr(is_lst, s1', p, s2', e', s3') ->
                  if is_var_pat p then (qb::qbs, ml) else begin
                    let ty = annot_to_typ p in                      
                    let n = pattern_gen gen p in
                    let p' = matrix_compile_mk_pvar n ty in
                    let qb' = Qb_restr(is_lst, s1', p', s2', e', s3') in
                    (qb' :: qbs, (n, ty, p) :: ml)
                  end) qbs ([], [])
   in
   let (vars_t, pats_t, wc_t) = begin
      let var_seplist = (Seplist.from_list (List.map (fun (n, ty, _) -> (matrix_compile_mk_var n ty, space)) ml)) in
      let pats_seplist = (Seplist.from_list (List.map (fun (_, _, p) -> (p, space)) ml)) in
      let tup_ty = { Types.t = Types.Ttup (List.map (fun (_, ty, _) -> ty) ml) } in
      let vars_t = C.mk_tup loc space var_seplist space (Some tup_ty) in
      let pats_t = C.mk_ptup loc space pats_seplist space (Some tup_ty) in
      let wc_t = matrix_compile_mk_pwild tup_ty in
      (vars_t, pats_t, wc_t)
    end in

    let casesL = (pats_t, e) :: (if (single_pat_exhaustive pats_t) then [] else [(wc_t, mk_tf_exp is_forall)]) in
    let cases = Seplist.from_list (List.map (fun (p, e) -> ((pat_append_lskips space p, space, e, loc), space)) casesL) in
    let case_exp =  C.mk_case false loc space vars_t space cases space (Some (exp_to_typ e)) in 

    let mk_case_exp e' = C.mk_case false loc space vars_t space (Seplist.from_list [((pats_t, space, e', loc), space)]) space (Some (exp_to_typ e')) in
    let case_expL = List.map mk_case_exp eL in
    (new_qbs, case_exp, case_expL);;

let remove_pat_restr_quant env comp e =   
  let loc = Ast.Trans(true, "remove_pat_restr_quant", Some (exp_to_locn e)) in
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  let qb_OK = (function | Qb_var _ -> true | Qb_restr(_,_,p,_,_,_) -> is_var_pat p) in
  match C.exp_to_term e with
  | Quant(q,qbs,s,e') ->
      if List.for_all qb_OK qbs then None else
        let is_forall = (match q with Ast.Q_forall _ -> true | _ -> false) in
        let (new_qbs, case_exp, _) = remove_pat_restr_quant_aux loc env qbs is_forall e' [] in
        let bool_ty = { Types.t = Types.Tapp ([], Path.boolpath) } in
           Some(C.mk_quant loc q new_qbs s (comp case_exp) (Some bool_ty))
  | _ -> None


(* Removes patterns from restricted quantification.
 * forall (p IN e). P x  goes to
 * forall x IN e. match x with p --> P x | _ -> true*)
let remove_comp_binding_pat_restr_quant env comp e = 
  let loc = Ast.Trans(true, "remove_comp_binding_pat_restr_quant", Some (exp_to_locn e)) in
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  let qb_OK = (function | Qb_var _ -> true | Qb_restr(_,_,p,_,_,_) -> is_var_pat p) in
  match C.exp_to_term e with
  | Comp_binding(is_lst,s1,e1,s2,s5,qbs,s3,e2,s4) ->
      if List.for_all qb_OK qbs then None else
        let (new_qbs, case_exp, case_expL) = remove_pat_restr_quant_aux loc env qbs false e2 [e1] in
        let e1' = match case_expL with [ee] -> comp ee | _ -> e1 in
           Some(C.mk_comp_binding loc is_lst s1 e1' s2 s5 new_qbs s3 (comp case_exp) s4 (Some (exp_to_typ e)))
  | _ -> None


let compile_exp topt mca env ctxt e =  
 let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
 let cf_opt e = compile_match_exp topt mca env e in
 let cf e = Util.option_default e (cf_opt e) in
 match C.exp_to_term e with 
   Case _ -> cf_opt e
 | Fun _ -> if mca.exp_OK env e then None else remove_fun env cf e
 | Function _ -> if mca.exp_OK env e then None else remove_function env cf e
 | Let _ -> if mca.exp_OK env e then None else remove_let env cf e
 | Quant _ -> if mca.exp_OK env e then None else remove_pat_restr_quant env cf e
 | Comp_binding _ -> if mca.exp_OK env e then None else remove_comp_binding_pat_restr_quant env cf e 
 | _ -> None


let compile_faux_seplist l env comp s s2_opt t topt org_d (sl : funcl_aux lskips_seplist) : val_def option = 
   let l = Ast.Trans(true, "compile_faux_seplist", Some l) in
   let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
   let (resorted, _, sll) = funcl_aux_seplist_group sl in
   let _ = if not resorted then () else Reporting.report_warning env (Reporting.Warn_fun_clauses_resorted (l, t, List.map (fun (n, _) -> Name.to_string n) sll, org_d)) in

   let sL = List.map (fun (_, sl) -> Seplist.to_list sl) sll in
   let sep = try Seplist.hd_sep sl with Failure _ -> None in

   let faux_OK (_, _, pL, _, _, _) = List.for_all is_var_pat pL in
   if (List.for_all (List.for_all faux_OK) sL) then None else
   begin

   let comp_funcl_aux_seplist (sl:funcl_aux list) : funcl_aux option = 
     match sl with [] -> None (* Should not happen, as funcl_aux_seplist_group should not return empty seplists *)
                   | ((nsa, c, pL, topt', _, e):funcl_aux) :: _ ->
   begin
     let gen = mk_var_name_gen (NameSetE.list_union (List.map (fun ((_, _, _, _, _, e):funcl_aux) -> nfmap_domain (C.exp_to_free e)) sl)) in
     let tyL = List.map annot_to_typ pL in
     let nL = List.map (pattern_gen gen) pL in
     let tup_ty = { Types.t = Types.Ttup tyL } in

     let pvarL = List.map2 matrix_compile_mk_pvar nL tyL in

     let var_seplist = (Seplist.from_list (List.map2 (fun n ty -> (matrix_compile_mk_var n ty, None)) nL tyL)) in
     let vars_t = C.mk_tup l space var_seplist None (Some tup_ty) in

     let process_row (_, _, pL, _, _, e) = begin
         let pats_seplist = (Seplist.from_list (List.map (fun p -> (p, None)) pL)) in
         let pats_t = C.mk_ptup l None pats_seplist space (Some tup_ty) in
         (pats_t, e) end in
     let case_exp = mk_case_exp false l vars_t (List.map process_row sl) (exp_to_typ e) in
     Some (nsa, c, pvarL, topt', space, comp case_exp)
   end in

   let funcl_auxL:funcl_aux list = Util.map_filter comp_funcl_aux_seplist sL in
   begin
   match funcl_auxL with
     | [] -> None
     | _ -> Some (Fun_def (s, s2_opt, topt, Seplist.from_list (List.map (fun fa -> (fa, sep)) funcl_auxL)))
   end
   end

let compile_def t mca env_global (_:Name.t list) env_local (((d, s), l, lenv) as org_d : def) =  
 let env = env_global in
 let cf_opt e = compile_match_exp t mca env e in
 let cf e = Util.option_default e (cf_opt e) in
 let constr topt s1 s2 sl =       
       Util.option_map (fun d -> (env_local, [(((Val_def d,s), l, lenv):def)]))
         (compile_faux_seplist l env cf s1 s2 t topt org_d sl) in
 if mca.def_OK env org_d then None else
 match d with
  |  Val_def (Fun_def (s1, s2_opt, topt, sl)) -> begin 
       if not (in_targets_opt t topt) then None else 
       constr topt s1 s2_opt sl
     end
  |  _ -> None
;;


(******************************************************************************)
(* Introduce pattern matching in function defs                                *)
(******************************************************************************)

(* Transforms let f y = match y with p1 -> e1 | ... | pn -> en into
   let rec f p1 = e1 
       and f p2 = e2 ... *)
  
let remove_toplevel_match targ mca env_global _ env_local (((d, s), l, lenv)) =
  let l_unk = Ast.Trans (true, "remove_toplevel_match", Some l) in
  let env = env_global in
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  let aux sk1 sk2_opt topt sl = begin
    let (_, sk_first_opt, group_nameL) = funcl_aux_seplist_group sl in
    let groupL = List.map (fun (_, x) -> x) group_nameL in
    let group_apply sl = if not (Seplist.length sl = 1) then None else   
    match Seplist.to_list sl with 
      | ([] | _ :: _ :: _) -> raise (Reporting_basic.err_unreachable l_unk "Not reachable, because of length check")
      | [(n,c,ps,topt,s,e)] -> 
          let e0 = strip_paren_typ_exp e in
          let e1 = Util.option_default e0 (compile_match_exp targ mca env e0) in
          let e2 = strip_paren_typ_exp e1 in
          (match C.exp_to_term e2 with Case(_,s1,e',s2,pats,s3) -> (       
          let free_vars_row s (p, _, ee, _) = NameSet.union s (NameSet.diff (nfmap_domain (C.exp_to_free ee)) (nfmap_domain p.rest.pvars)) in
          let free = List.fold_left free_vars_row NameSet.empty (Seplist.to_list pats) in
          match collapse_nested_matches_dest_pat_fun l_unk env free ps [e'] with None -> None | Some dest_f ->
          begin 
            let adapt_ws_pL pL = List.map (fun p -> let (p', _) = pat_alter_init_lskips space_com_init_ws p in p') pL in
            let work_row ((p, _, ee, _) : (pat * lskips * exp * Ast.l)) : funcl_aux option =
              Util.option_map (fun pL -> (n, c, adapt_ws_pL pL, topt, s, ee)) (dest_f [p]) in
            let sl_opt = Util.map_all (fun r -> Util.option_map (fun x -> (x, new_line)) (work_row r)) (Seplist.to_list pats) in
            Util.option_map Seplist.from_list sl_opt
          end)
          | _ -> None) in
    match (Util.map_changed group_apply groupL) with None -> None | Some sll' ->
      let sl' = Seplist.flatten space sll' in
      let new_d = ((Val_def ((Fun_def (sk1, sk2_opt, topt, sl'))), s), l, lenv) in
      if mca.def_OK env new_d then Some (env_local, [new_d]) else None
  end in
  match d with 
  |  Val_def ((Fun_def (sk1, sk2_opt, topt, sl))) -> begin 
       aux sk1 sk2_opt topt sl 
     end
  | _ -> None
;;

(******************************************************************************)
(* Define what should be compiled away for different backends                 *)
(******************************************************************************)


(* Arguments for compile_match_exp for different backends *)
let is_isabelle_pat_direct env (p : pat) : bool = 
  match p.term with
    | P_as _ -> false
    | P_num_add (_, _, _, i) -> i <= max_succ_nesting
    | P_record _ -> false
    | (P_vector _ | P_vectorC _) -> false
    | P_const (c, _) -> is_buildin_constructor Ast.Unknown env (Target.Target_no_ident Target.Target_isa) c.descr
    | P_lit li -> 
      begin
         match li.term with 
             (* string patterns are supported in principle, but lead to an explosion in Isabelle,
                because for each character in the string pattern, all 256 possible values of this char
                become separate cases. *)
           | L_string  _ -> false 
           | L_num (_, i, _) -> i <= max_succ_nesting 
           | _ -> true
      end
    | _ -> true
let is_isabelle_pat env = for_all_subpat (is_isabelle_pat_direct env)

let is_isabelle_exp env (e : exp) : bool = 
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  match C.exp_to_term e with
    | Let(_,(Let_fun _,_),_,_) -> false
    | Let(_,(Let_val (p,_,_,_),_),_,_) -> is_var_wild_tup_pat p
    | Fun (_, pL, _, _) -> List.for_all is_var_wild_tup_pat pL
    | Function _ -> false
    | Case _ -> true
    | Quant (_, qbs, _, _) -> List.for_all (function | Qb_var _ -> true | Qb_restr(_,_,p,_,_,_) -> is_var_wild_tup_pat p) qbs
    | Comp_binding(_,_,_,_,_,qbs,_,_,_) -> List.for_all (function | Qb_var _ -> true | Qb_restr(_,_,p,_,_,_) -> is_var_wild_tup_pat p) qbs
    | _ -> false

let is_pat_match_def mcf mpcf env (d:def) =
  let mL = def_to_pat_matrix_list d in
  let check_fun (_, (_, m), l) = 
    ((match (check_match_internal l env  (Reporting.Warn_source_def d) m) with None -> true | Some mp -> mpcf mp) &&
    (List.for_all (mcf env) (pat_matrix_pats m)))
  in
  List.for_all check_fun mL

let is_isabelle_def = 
  is_pat_match_def is_isabelle_pat (fun mp -> mp.redundant_pats = [])

let is_isabelle_pattern_match:match_check_arg = 
   { exp_OK = (fun env e -> is_isabelle_exp env e &&
                  (match check_match_exp env e with Some mp -> mp.redundant_pats = [] | None -> true));
     def_OK = is_isabelle_def;
     pat_OK = (fun env p -> is_isabelle_pat env p);
     allow_redundant = false;
     allow_non_exhaustive = true }

let is_hol_exp env (e : exp) : bool = 
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  match C.exp_to_term e with
    | Let(_,(Let_fun _,_),_,_) -> false
    | Let(_,(Let_val (p,_,_,_),_),_,_) -> is_var_tup_pat p
    | Fun (_, pL, _, _) -> List.for_all is_var_tup_pat pL
    | Function _ -> false
    | Case _ -> true
    | Quant (_, qbs, _, _) -> List.for_all (function | Qb_var _ -> true | Qb_restr(_,_,p,_,_,_) -> is_var_tup_pat p) qbs
    | Comp_binding(_,_,_,_,_,qbs,_,_,_) -> List.for_all (function | Qb_var _ -> true | Qb_restr(_,_,p,_,_,_) -> is_var_tup_pat p) qbs
    | _ -> false

let is_hol_pat_direct env (p : pat) : bool = 
  match p.term with
    | P_num_add (_, _, _, i) -> i <= max_succ_nesting
    | P_as _ -> false
    | P_record _ -> false
    | (P_vector _ | P_vectorC _) -> false
    | P_lit li -> 
      begin
         match li.term with 
           | L_num (_, i, _) -> i <= max_succ_nesting 
           | _ -> true
      end
    | P_const (c, _) -> is_buildin_constructor Ast.Unknown env (Target.Target_no_ident Target.Target_hol) c.descr
    | _ -> true
let is_hol_pat env = for_all_subpat (is_hol_pat_direct env)

let is_hol_def = 
  is_pat_match_def is_hol_pat (fun mp -> mp.redundant_pats = [])

let is_hol_pattern_match:match_check_arg = 
   { exp_OK = (fun env e -> is_hol_exp env e &&
                  (match check_match_exp env e with Some mp -> mp.redundant_pats = [] | None -> true));
     def_OK = is_hol_def;
     pat_OK = is_hol_pat;
     allow_redundant = false;
     allow_non_exhaustive = true }

let is_pattern_match_const b : match_check_arg = 
   { exp_OK = (fun _ _ -> b);
     def_OK = (fun _ _ -> b);
     pat_OK = (fun _ _ -> b);
     allow_redundant = b;
     allow_non_exhaustive = b }

let is_ocaml_pat_direct env (p : pat) : bool = 
  match p.term with
    | P_num_add _ -> false
    | (P_vector _ | P_vectorC _) -> false
    | P_lit li -> 
      begin
         match li.term with 
           | L_num _ -> (p.typ = nat_ty) (* only nat constants work *)
           | _ -> true
      end
    | P_const (c, _) -> is_buildin_constructor Ast.Unknown env (Target.Target_no_ident Target.Target_ocaml) c.descr
    | _ -> true

let is_ocaml_pat env = for_all_subpat (is_ocaml_pat_direct env)

let is_ocaml_exp env (e : exp) : bool = 
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  match C.exp_to_term e with
    | Let(_,(Let_fun (_, pL, _, _, _),_),_,_) -> List.for_all (is_ocaml_pat env) pL
    | Let(_,(Let_val (p,_,_,_),_),_,_) -> is_ocaml_pat env p
    | Fun (_, pL, _, _) -> List.for_all (is_ocaml_pat env) pL
    | Function (_, rows, _) ->  Seplist.for_all (fun (p, _, _, _) -> (is_ocaml_pat env) p) rows
    | Case _ -> true
    | Quant (_, qbs, _, _) -> List.for_all (function | Qb_var _ -> true | Qb_restr(_,_,p,_,_,_) -> is_ocaml_pat env p) qbs
    | Comp_binding(_,_,_,_,_,qbs,_,_,_) -> List.for_all (function | Qb_var _ -> true | Qb_restr(_,_,p,_,_,_) -> is_ocaml_pat env p) qbs
    | _ -> false

let is_ocaml_def = is_pat_match_def is_ocaml_pat (fun mp -> true)

let is_ocaml_pattern_match:match_check_arg = 
   { exp_OK = (fun env e -> is_ocaml_exp env e);
     def_OK = is_ocaml_def;
     pat_OK = (fun env p -> is_ocaml_pat env p);
     allow_redundant = true;
     allow_non_exhaustive = true }

let coq_num_lit_types = [nat_ty; natural_ty]
let is_coq_pat_direct (toplevel : bool) env (p : pat) : bool = 
  match p.term with
    | P_record _ -> false
    | P_tup _ -> not toplevel
    | (P_vector _ | P_vectorC _) -> false
    | P_const (c, _) -> not toplevel
    | _ -> true

let rec is_coq_exp env (e : exp) : bool = 
  let module C = Exps_in_context(struct let env_opt = Some env let avoid = None end) in
  match C.exp_to_term e with
    | Let(_,(Let_fun _,_),_,_) -> false
    | Let(_,(Let_val (p,_,_,e),_),_,_) -> is_var_wild_pat p && is_coq_exp env e
    | Fun (_, pL, _, _) -> List.for_all is_var_wild_pat pL
    | Function _ -> false
    | Case _ -> true
    | Quant (_, qbs, _, _) -> List.for_all (function | Qb_var _ -> true | Qb_restr(_,_,p,_,_,_) -> is_var_wild_pat p) qbs
    | _ -> false
;;

let is_coq_pat toplevel env = for_all_subpat (is_coq_pat_direct toplevel env)
let is_coq_def = is_pat_match_def (is_coq_pat true) (fun mp -> mp.redundant_pats = [] && mp.is_exhaustive)

let is_coq_pattern_match : match_check_arg = 
   { exp_OK = (fun env e -> is_coq_exp env e &&
                 (match check_match_exp env e with Some mp -> mp.redundant_pats = [] && mp.is_exhaustive | None -> true));
     def_OK = is_coq_def;
     pat_OK = is_coq_pat false;
     allow_redundant = false;
     allow_non_exhaustive = false }
