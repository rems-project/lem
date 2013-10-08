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

open Output
open Typed_ast
open Typed_ast_syntax
open Target_binding

let r = Ulib.Text.of_latin1
let marker_lex_skip : Ast.lex_skips = (Some [Ast.Ws (Ulib.Text.of_latin1 "***marker***")])

(* Resolve a const identifier stored inside a id, with a full one in case of Id_none *)
let resolve_constant_id_ident env id : Ident.t =
  match id.id_path with 
      | Id_none sk -> resolve_const_ref env sk id.descr
      | Id_some id -> id

let resolve_type_id_ident env id path : Ident.t =
  match id.id_path with 
      | Id_none sk -> resolve_type_path env sk path
      | Id_some id -> id

let resolve_module_id_ident env id path : Ident.t =
  match id.id_path with 
      | Id_none sk -> resolve_module_path env sk path
      | Id_some id -> id


let cr_special_uncurry_fun n oL = begin
  if not (List.length oL = n + 1) then
     raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal (Ast.Unknown, "target presentation of OCaml constructor got the wrong number of args")))
  else if (n = 0) then oL else
  if (n = 1) then
     [List.nth oL 0; texspace; List.nth oL 1]
  else
     [List.hd oL; texspace; meta "("] @
      Util.intercalate (meta ",") (List.tl oL) @
     [meta ")"]
  end


let cr_special_fun_to_fun = function
  CR_special_uncurry n -> cr_special_uncurry_fun n


(** Axiliary function for [inline_exp] *)
let rec build_subst (params : name_lskips_annot list) (args : exp list) 
      : exp_subst Nfmap.t * name_lskips_annot list * exp list =
  match (params, args) with
    | ([],args) -> (Nfmap.empty, [], args)
    | (params, []) -> (Nfmap.empty, params, [])
    | (p::params, a::args) ->
        let (subst, x, y) = build_subst params args in
          (Nfmap.insert subst (Name.strip_lskip p.term, Sub(a)), x, y)

let inline_exp l (target : Target.non_ident_target) env was_infix params body tsubst (args : exp list) =
  let module C = Exps_in_context(struct let env_opt = Some env;; let avoid = None end) in
  let loc = Ast.Trans(false, "inline_exp", Some l) in
  let (vsubst, leftover_params, leftover_args) = build_subst params args in
  let b = C.exp_subst (tsubst,vsubst) body in
  let stays_infix = match C.exp_to_term b with
    | Constant id -> Precedence.is_infix (Precedence.get_prec (Target.Target_no_ident target) env id.descr)
    | _ -> false
  in
  if params = [] && was_infix && stays_infix then
  begin
    (* Turn infix operators into infix operators again *)
    match leftover_args with
      | [a1; a2] -> C.mk_infix loc a1 b a2 None
      | _ -> raise (Reporting_basic.err_unreachable false Ast.Unknown "infix operator with not 2 arguments")
  end else 
  if leftover_params = [] then
    (* all parameters are instantiatated *)
    (List.fold_left 
       (fun e e' -> C.mk_app loc e e' None)
       b
       leftover_args)
   else
     (C.mk_fun loc
         None (List.map (fun n -> C.mk_pvar n.locn n.term (Types.type_subst tsubst n.typ))
                                  leftover_params) 
         None b None)


let inline_exp_macro (target : Target.non_ident_target) env e =
  let l_unk = Ast.Trans(false, "do_substitutions", Some (exp_to_locn e)) in
  let module C = Exps_in_context(struct let env_opt = Some env;; let avoid = None end) in
  let (f,args,was_infix) = strip_app_infix_exp e in
    match C.exp_to_term f with
      | Constant(c_id) ->
          let cd = c_env_lookup l_unk env.c_env c_id.descr in
          begin            
            match Target.Targetmap.apply cd.target_rep target with
              | Some(CR_inline (_, params,body)) ->
                  let tsubst = Types.TNfmap.from_list2 cd.const_tparams c_id.instantiation in

                  (* adapt whitespace before body *)
                  let b = (fst (alter_init_lskips (fun _ -> (ident_get_lskip c_id, None)) body)) in
                  Some (inline_exp l_unk target env was_infix params b tsubst args)
              | _ -> None
          end
      | _ -> None


module Make(A : sig 
  val env : env;; 
  val target : Target.target;;
  val id_format_args : (bool -> Output.id_annot -> Ulib.Text.t -> Output.t) * Output.t
 end) = struct



(** An auxiliary, temporary function to strip the artifacts of the library structure.
    Hopefully, this won't be necessary much longer, when the library gets redesigned. *)
let strip_library_prefix =
  match A.target with
    | Target.Target_ident -> (fun i -> i)
    | Target.Target_no_ident t -> 
         let n_t = Target.non_ident_target_to_mname t in
      fun i -> begin
         let i = Ident.strip_path n_t i in  
         i
      end


(** TODO: add renaming of modules here later.
          remove intermediate stripping of library prefix *)
let fix_module_prefix_ident env i =
  strip_library_prefix i


let ident_to_output use_infix =
  let (ident_f, sep) = A.id_format_args in 
  Ident.to_output_format (ident_f use_infix) Term_const sep


(* A version of const_id_to_ident that returns additionally, whether
   the ascii-alternative was used. This is handly for determining infix
   status. *)
let const_id_to_ident_aux c_id ascii_alternative =
  let l = Ast.Trans (false, "const_id_to_ident", None) in
  let c_descr = c_env_lookup l A.env.c_env c_id.descr in
  let org_ident = resolve_constant_id_ident A.env c_id in
    match (c_descr.ascii_rep, ascii_alternative) with
      | (Some ascii, true) -> (true, Ident.rename org_ident ascii) 
      | _                  ->
          let i = match Target.Targetmap.apply_target c_descr.target_rep A.target with
             | None -> org_ident
             | Some (CR_new_ident (_, _, i)) -> i
             | Some (CR_rename (_, _, n)) -> Ident.rename org_ident n
             | Some (CR_inline _) -> raise (Reporting_basic.err_unreachable false l "Inlining should have already been done by Macro")
             | Some (CR_special (_, _, _, n, _, _)) -> Ident.rename org_ident n
          in
          let i' = fix_module_prefix_ident (A.env.local_env) i in
          (false, i')
;;

let const_id_to_ident c_id ascii_alternative = snd (const_id_to_ident_aux c_id ascii_alternative)

let constant_application_to_output_simple is_infix_pos arg_f args c_id ascii_alternative = begin
  let (ascii_used, i) = const_id_to_ident_aux c_id ascii_alternative in 
  let const_is_infix = not (ascii_used) && Precedence.is_infix (Precedence.get_prec A.target A.env c_id.descr) in 
  let is_infix = (is_infix_pos && const_is_infix && (Ident.has_empty_path_prefix i)) in
  let use_infix_notation = ((not is_infix) && const_is_infix) in
  let name = ident_to_output use_infix_notation i in
  let args_out = List.map (arg_f use_infix_notation) args in
  if (not is_infix) then
     (name :: args_out) 
  else 
     [(List.nth args_out 0); name; (List.nth args_out 1)]
end

(* assumes that there are enough arguments, otherwise list_split_after will fail *)
let constant_application_to_output_special c_id to_out arg_f args vars : Output.t list =
  let i = const_id_to_ident c_id false in
  let name = ident_to_output false i in
  let args_output = List.map arg_f args in
  let (o_vars, o_rest) = Util.split_after (List.length vars) args_output (* assume there are enough elements *) in
  let o_fun = (cr_special_fun_to_fun to_out) (name :: o_vars) in
  o_fun @ o_rest


let function_application_to_output l (arg_f0 : exp -> Output.t) (is_infix_pos : bool) (full_exp : exp) (c_id : const_descr_ref id) (args : exp list) (ascii_alternative: bool) : Output.t list =
  let _ = if is_infix_pos && not (List.length args = 2) then (raise (Reporting_basic.err_unreachable false Ast.Unknown "Infix position with wrong number of args")) else () in
  let arg_f b e = if b then arg_f0 (mk_opt_paren_exp e) else arg_f0 e in
  let c_descr = c_env_lookup Ast.Unknown A.env.c_env c_id.descr in
  match Target.Targetmap.apply_target c_descr.target_rep A.target with
     | Some (CR_special (_, _, _, _, to_out, vars)) when not ascii_alternative -> 
            if (List.length args < List.length vars) then begin
              (* eta expand and call recursively *)
              let remaining_vars = Util.list_dropn (List.length args) vars in
              let eta_exp = mk_eta_expansion_exp (A.env.t_env) remaining_vars full_exp in
              [arg_f true eta_exp]
              
            end else begin
              constant_application_to_output_special c_id to_out (arg_f false) args vars 
            end
     | _ -> constant_application_to_output_simple is_infix_pos arg_f args c_id ascii_alternative

let pattern_application_to_output (arg_f0 : pat -> Output.t) (c_id : const_descr_ref id) (args : pat list) (ascii_alternative : bool) : Output.t list =
  let arg_f b p = if b then arg_f0 (Pattern_syntax.mk_opt_paren_pat p) else arg_f0 p in
  let c_descr = c_env_lookup Ast.Unknown A.env.c_env c_id.descr in
  match Target.Targetmap.apply_target c_descr.target_rep A.target with
     | Some (CR_special (_, _, _, _, to_out, vars)) when not ascii_alternative -> 
        if (List.length args < List.length vars) then begin
           raise (Reporting_basic.err_unreachable true Ast.Unknown "Constructor without enough arguments!")
        end else begin
           constant_application_to_output_special c_id to_out (arg_f false) args vars 
        end
     | _ -> constant_application_to_output_simple false arg_f args c_id ascii_alternative

let type_path_to_name n0 (p : Path.t) : Name.lskips_t =
  let l = Ast.Trans (false, "type_path_to_name", None) in
  let td = Types.type_defs_lookup l A.env.t_env p in
  let n = type_descr_to_name A.target p td in
  let n' = Name.replace_lskip (Name.add_lskip n) (Name.get_lskip n0) in
  n'

let type_id_to_ident (p : Path.t id) =
   let l = Ast.Trans (false, "type_id_to_ident", None) in
   let td = Types.type_defs_lookup l A.env.t_env p.descr in
   let org_type = resolve_type_id_ident A.env.local_env p p.descr in
   let i = match Target.Targetmap.apply_target td.Types.type_target_rep A.target with
     | None -> org_type
     | Some (Types.TR_new_ident (_, _, i)) -> i 
     | Some (Types.TR_rename (_, _, n)) -> Ident.rename org_type n in
   let i' = fix_module_prefix_ident A.env.local_env i in
   i'

let type_id_to_ident_no_modify (p : Path.t id) =
  let (ns, n) = Path.to_name_list p.descr in
  let sk = ident_get_lskip p in
  Ident.mk_ident sk ns n


let module_id_to_ident (mod_descr : mod_descr id) : Ident.t =
(*   let l = Ast.Trans ("module_id_to_ident", None) in *)
   let i = resolve_module_id_ident (A.env.local_env) mod_descr mod_descr.descr.mod_binding in
   let i' = fix_module_prefix_ident (A.env.local_env) i in
   i'

let const_ref_to_name n0 c =
  let l = Ast.Trans (false, "const_ref_to_name", None) in
  let c_descr = c_env_lookup l A.env.c_env c in
  let (_, n) = constant_descr_to_name A.target c_descr in
  let n' = Name.replace_lskip (Name.add_lskip n) (Name.get_lskip n0) in
  n'

end

let component_to_output t = 
  let open Output in
    let a = Output.Target in
    match t with
      | Ast.Component_type s -> ws s ^ id a (r"type")
      | Ast.Component_field s -> ws s ^ id a (r"field")
      | Ast.Component_module s -> ws s ^ id a (r"module")
      | Ast.Component_function s -> ws s ^ id a (r"function")
