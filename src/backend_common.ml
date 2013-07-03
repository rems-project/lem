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


(** Axiliary function for [inline_exp] *)
let rec build_subst (params : name_lskips_annot list) (args : exp list) 
      : exp_subst Nfmap.t * name_lskips_annot list * exp list =
  match (params, args) with
    | ([],args) -> (Nfmap.empty, [], args)
    | (params, []) -> (Nfmap.empty, params, [])
    | (p::params, a::args) ->
        let (subst, x, y) = build_subst params args in
          (Nfmap.insert subst (Name.strip_lskip p.term, Sub(a)), x, y)

let inline_exp l target_opt env was_infix params body tsubst (args : exp list) =
  let module C = Exps_in_context(struct let env_opt = Some env;; let avoid = None end) in
  let loc = Ast.Trans("inline_exp", Some l) in
  let (vsubst, leftover_params, leftover_args) = build_subst params args in
  let b = C.exp_subst (tsubst,vsubst) body in
  let stays_infix = match C.exp_to_term b with
    | Constant id -> Precedence.is_infix (Precedence.get_prec target_opt env id.descr)
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


let inline_exp_macro target_opt env e =
  let l_unk = Ast.Trans("do_substitutions", Some (exp_to_locn e)) in
  let module C = Exps_in_context(struct let env_opt = Some env;; let avoid = None end) in
  let (f,args,was_infix) = strip_app_infix_exp e in
    match C.exp_to_term f with
      | Constant(c_id) ->
          let cd = c_env_lookup l_unk env.c_env c_id.descr in
          begin            
            match Target.Targetmap.apply_opt cd.target_rep target_opt with
              | Some(CR_inline (_, params,body)) ->
                  let tsubst = Types.TNfmap.from_list2 cd.const_tparams c_id.instantiation in

                  (* adapt whitespace before body *)
                  let b = (fst (alter_init_lskips (fun _ -> (ident_get_first_lskip c_id, None)) body)) in
                  Some (inline_exp l_unk target_opt env was_infix params b tsubst args)
              | _ -> None
          end
      | _ -> None


module Make(A : sig 
  val env : env;; 
  val target_opt : Target.target option;;
  val id_format_args : (Output.id_annot -> Ulib.Text.t -> Output.t) * Output.t
 end) = struct


let ident_to_output use_infix =
  let (ident_f, sep) = A.id_format_args in 
  if use_infix then
    Ident.to_output_infix ident_f Term_const sep
  else 
    Ident.to_output Term_const sep 


let const_id_to_ident c_id =
  let l = Ast.Trans ("const_id_to_ident", None) in
  let c_descr = c_env_lookup l A.env.c_env c_id.descr in
  let i = match Target.Targetmap.apply_opt c_descr.target_rep A.target_opt with
     | None -> resolve_ident_path c_id c_descr.const_binding
     | Some (CR_new_ident (_, _, i)) -> i
     | Some (CR_rename (_, _, n)) -> Ident.rename (resolve_ident_path c_id c_descr.const_binding) n
     | Some (CR_inline _) -> raise (Reporting_basic.err_unreachable false l "Inlining should have already been done by Macro")
     | Some (CR_special (_, _, _, n, _, _)) -> Ident.rename (resolve_ident_path c_id c_descr.const_binding) n
  in
  i

let constant_application_to_output_simple is_infix_pos arg_f args c_id = begin
  let i = const_id_to_ident c_id in 
  let const_is_infix = Precedence.is_infix (Precedence.get_prec A.target_opt A.env c_id.descr) in
  let is_infix = (is_infix_pos && const_is_infix && (Ident.has_empty_path_prefix i)) in
  let use_infix_notation = ((not is_infix) && const_is_infix) in
  let name = ident_to_output use_infix_notation i in
  let args_out = List.map arg_f args in
  if (not is_infix) then
     (name :: args_out) 
  else 
     [(List.nth args_out 0); name; (List.nth args_out 1)]
end

(* assumes that there are enough arguments, otherwise list_split_after will fail *)
let constant_application_to_output_special c_id to_out arg_f args vars : Output.t list =
  let name = ident_to_output false (const_id_to_ident c_id) in
  let args_output = List.map arg_f args in
  let (o_vars, o_rest) = Util.split_after (List.length vars) args_output (* assume there are enough elements *) in
  let o_fun = to_out (name :: o_vars) in
  o_fun @ o_rest


let function_application_to_output (arg_f : exp -> Output.t) (is_infix_pos : bool) (c_id : const_descr_ref id) (args : 'a list) : Output.t list =
  let _ = if is_infix_pos && not (List.length args = 2) then (raise (Reporting_basic.err_unreachable false Ast.Unknown "Infix position with wrong number of args")) else () in

  let c_descr = c_env_lookup Ast.Unknown A.env.c_env c_id.descr in
  match Target.Targetmap.apply_opt c_descr.target_rep A.target_opt with
     | Some (CR_special (_, _, _, _, to_out, vars)) -> 
            if (List.length args < List.length vars) then begin
              raise (Reporting_basic.err_todo true Ast.Unknown "Special function syntax needs fun-introduction!")
            end else begin
              constant_application_to_output_special c_id to_out arg_f args vars 
            end
     | _ -> constant_application_to_output_simple is_infix_pos arg_f args c_id

let pattern_application_to_output (arg_f : pat -> Output.t) (c_id : const_descr_ref id) (args : pat list) : Output.t list =
  let c_descr = c_env_lookup Ast.Unknown A.env.c_env c_id.descr in
  match Target.Targetmap.apply_opt c_descr.target_rep A.target_opt with
     | Some (CR_special (_, _, _, _, to_out, vars)) -> 
        if (List.length args < List.length vars) then begin
           raise (Reporting_basic.err_unreachable true Ast.Unknown "Constructor without enough arguments!")
        end else begin
           constant_application_to_output_special c_id to_out arg_f args vars 
        end
     | _ -> constant_application_to_output_simple false arg_f args c_id

let type_id_to_ident (p : Path.t id) =
   let l = Ast.Trans ("type_id_to_ident", None) in
   let td = Types.type_defs_lookup l A.env.t_env p.descr in
   match Target.Targetmap.apply_opt td.Types.type_target_rep A.target_opt with
     | None -> resolve_ident_path p p.descr
     | Some (Types.TR_new_ident (_, _, i)) -> i 
     | Some (Types.TR_rename (_, _, n)) -> Ident.rename (resolve_ident_path p p.descr) n

let const_ref_to_name n0 c =
  let l = Ast.Trans ("const_ref_to_name", None) in
  let c_descr = c_env_lookup l A.env.c_env c in
  let (_, n) = constant_descr_to_name A.target_opt c_descr in
  let n' = Name.replace_lskip (Name.add_lskip n) (Name.get_lskip n0) in
  n'

let type_path_to_name n0 (p : Path.t) : Name.lskips_t =
  let l = Ast.Trans ("type_path_to_name", None) in
  let td = Types.type_defs_lookup l A.env.t_env p in
  let n = type_descr_to_name A.target_opt p td in
  let n' = Name.replace_lskip (Name.add_lskip n) (Name.get_lskip n0) in
  n'


end
