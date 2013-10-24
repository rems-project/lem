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
open Types

let r = Ulib.Text.of_latin1
let marker_lex_skip : Ast.lex_skips = (Some [Ast.Ws (Ulib.Text.of_latin1 "***marker***")])

(* Resolve a const identifier stored inside a id, with a full one in case of Id_none *)
let resolve_constant_id_ident l env id : Ident.t =
  match id.id_path with 
      | Id_none sk -> resolve_const_ref l env sk id.descr
      | Id_some id -> id

let resolve_type_id_ident l env id path : Ident.t =
  match id.id_path with 
      | Id_none sk -> resolve_type_path l env sk path
      | Id_some id -> id

let resolve_module_id_ident l env id path : Ident.t =
  match id.id_path with 
      | Id_none sk -> resolve_module_path l env sk path
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

let inline_exp l (target : Target.target) env was_infix params body tsubst (args : exp list) =
  let module C = Exps_in_context(struct let env_opt = Some env;; let avoid = None end) in
  let loc = Ast.Trans(false, "inline_exp", Some l) in
  let (vsubst, leftover_params, leftover_args) = build_subst params args in
  let b = C.exp_subst (tsubst,vsubst) body in
  let stays_infix = Precedence.is_infix (Precedence.get_prec_exp target env b) in
  if params = [] && was_infix && stays_infix then
  begin
    (* Turn infix operators into infix operators again *)
    match leftover_args with
      | [a1; a2] -> C.mk_infix loc a1 b a2 None
      | _ -> raise (Reporting_basic.err_unreachable l "infix operator with not 2 arguments")
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


let generalised_inline_exp_macro (do_CR_simple : bool) (target : Target.target) env e =
  let l_unk = Ast.Trans(false, "inline_exp_macro", Some (exp_to_locn e)) in
  let module C = Exps_in_context(struct let env_opt = Some env;; let avoid = None end) in
  let (f,args,was_infix) = strip_app_infix_exp e in
    match C.exp_to_term f with
      | Constant(c_id) ->
          let cd = c_env_lookup l_unk env.c_env c_id.descr in
          let do_it (params, body) : exp =
            let tsubst = Types.TNfmap.from_list2 cd.const_tparams c_id.instantiation in
   
            (* adapt whitespace before body *)
            let b = (fst (alter_init_lskips (fun _ -> (ident_get_lskip c_id, None)) body)) in
            inline_exp l_unk target env was_infix params b tsubst args
          in

          let subst_opt = begin            
            match Target.Targetmap.apply_target cd.target_rep target with
              | Some(CR_inline (_, _, params,body)) -> Some (params, body)
              | Some(CR_simple (_, _, params,body)) when do_CR_simple -> Some (params, body)
              | _ -> None
          end in
          Util.option_map do_it subst_opt
      | _ -> None


let inline_exp_macro (target : Target.non_ident_target) env ctxt e =
  generalised_inline_exp_macro false (Target.Target_no_ident target) env e


let get_module_name env target path mod_name =  begin
  let md = lookup_mod_descr env path mod_name in
  match Target.Targetmap.apply_target md.mod_target_rep target with
    | Some (MR_rename (_, n)) -> n
    | _ -> mod_name
end

module Make(A : sig 
  val env : env;; 
  val target : Target.target;;
  val id_format_args : (bool -> Output.id_annot -> Ulib.Text.t -> Output.t) * Output.t
 end) = struct

let fix_module_name_list nl = begin
  let rec aux acc path rest = match rest with
    | [] -> List.rev acc
    | m :: rest' ->
        aux ((get_module_name A.env A.target path m)::acc) (path @ [m]) rest'
  in
  aux [] [] nl
end

let fix_module_prefix_ident (i : Ident.t) =
  let (ns, n) = Ident.to_name_list i in
  let ns' = fix_module_name_list ns in
  Ident.mk_ident (Ident.get_lskip i) ns' n

let fix_module_ident (i : Ident.t) =
  let (ns, n) = Ident.to_name_list i in
  let ns' = fix_module_name_list ns in
  let n' = get_module_name A.env A.target ns n in
  Ident.mk_ident (Ident.get_lskip i) ns' n'

let ident_to_output use_infix =
  let (ident_f, sep) = A.id_format_args in 
  Ident.to_output_format (ident_f use_infix) Term_const sep


let const_ref_to_name n0 use_ascii c =
  let l = Ast.Trans (false, "const_ref_to_name", None) in
  let c_descr = c_env_lookup l A.env.c_env c in
  let (_, n_no_ascii, n_ascii_opt) = constant_descr_to_name A.target c_descr in
  let n =    
    match (n_ascii_opt, use_ascii) with
      | (Some ascii, true) -> ascii
      | _  -> n_no_ascii
  in
  let n' = Name.replace_lskip (Name.add_lskip n) (Name.get_lskip n0) in
  n'


(* A version of const_id_to_ident that returns additionally, whether
   the ascii-alternative was used. This is handy for determining infix
   status. *)
let const_id_to_ident_aux c_id ascii_alternative given_id_opt =   
  let l = Ast.Trans (false, "const_id_to_ident", None) in
  let c_descr = c_env_lookup l A.env.c_env c_id.descr in
  let org_ident = resolve_constant_id_ident l A.env c_id in
  let (_, n, n_ascii_opt) = constant_descr_to_name A.target c_descr in
  let (ascii_used, ident') =    
    match (n_ascii_opt, ascii_alternative, given_id_opt) with
      | (Some ascii, true, _) -> (true, Ident.rename org_ident ascii)
      | (_, false, Some i) -> (false, Ident.replace_lskip i (Ident.get_lskip org_ident))
      | _  -> (false, Ident.rename org_ident n)
  in
  let ident = fix_module_prefix_ident ident' in
  (ascii_used, ident)
;;

let const_id_to_ident c_id ascii_alternative = snd (const_id_to_ident_aux c_id ascii_alternative None)

let constant_application_to_output_simple is_infix_pos arg_f args c_id ascii_alternative given_id_opt = begin
  let (ascii_used, i) = const_id_to_ident_aux c_id ascii_alternative given_id_opt in 
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
  let _ = if is_infix_pos && not (List.length args = 2) then (raise (Reporting_basic.err_unreachable l "Infix position with wrong number of args")) else () in
  let arg_f b e = if b then arg_f0 (mk_opt_paren_exp e) else arg_f0 e in
  let c_descr = c_env_lookup Ast.Unknown A.env.c_env c_id.descr in
  match Target.Targetmap.apply_target c_descr.target_rep A.target with
     | Some (CR_special (_, _, to_out, vars)) when not ascii_alternative -> 
            if (List.length args < List.length vars) then begin
              (* eta expand and call recursively *)
              let remaining_vars = Util.list_dropn (List.length args) vars in
              let eta_exp = mk_eta_expansion_exp (A.env.t_env) remaining_vars full_exp in
              [arg_f true eta_exp]
              
            end else begin
              constant_application_to_output_special c_id to_out (arg_f false) args vars 
            end
     | Some (CR_simple (_, _, params,body)) when not ascii_alternative -> begin
         let tsubst = Types.TNfmap.from_list2 c_descr.const_tparams c_id.instantiation in
         let b = (fst (alter_init_lskips (fun _ -> (ident_get_lskip c_id, None)) body)) in
         let new_exp = inline_exp l A.target A.env is_infix_pos params b tsubst args in
         [arg_f true new_exp]
       end
     | Some (CR_infix (_, _, _, i)) -> constant_application_to_output_simple is_infix_pos arg_f args c_id ascii_alternative (Some i)
     | _ -> constant_application_to_output_simple is_infix_pos arg_f args c_id ascii_alternative None

let pattern_application_to_output (arg_f0 : pat -> Output.t) (c_id : const_descr_ref id) (args : pat list) (ascii_alternative : bool) : Output.t list =
  let arg_f b p = if b then arg_f0 (Pattern_syntax.mk_opt_paren_pat p) else arg_f0 p in
  let c_descr = c_env_lookup Ast.Unknown A.env.c_env c_id.descr in
  match Target.Targetmap.apply_target c_descr.target_rep A.target with
     | Some (CR_special (_, _, to_out, vars)) when not ascii_alternative -> 
        if (List.length args < List.length vars) then begin
           raise (Reporting_basic.err_unreachable Ast.Unknown "Constructor without enough arguments!")
        end else begin
           constant_application_to_output_special c_id to_out (arg_f false) args vars 
        end
     | _ -> constant_application_to_output_simple false arg_f args c_id ascii_alternative None

let type_path_to_name n0 (p : Path.t) : Name.lskips_t =
  let l = Ast.Trans (false, "type_path_to_name", None) in
  let td = Types.type_defs_lookup l A.env.t_env p in
  let n = type_descr_to_name A.target p td in
  let n' = Name.replace_lskip (Name.add_lskip n) (Name.get_lskip n0) in
  n'

let type_id_to_ident (p : Path.t id) =
   let l = Ast.Trans (false, "type_id_to_ident", None) in
   let td = Types.type_defs_lookup l A.env.t_env p.descr in
   let org_type = resolve_type_id_ident l A.env p p.descr in
   match Target.Targetmap.apply_target td.Types.type_rename A.target with
     | Some (_, n) -> fix_module_prefix_ident (Ident.rename org_type n)
     | None -> begin
         match Target.Targetmap.apply_target td.Types.type_target_rep A.target with
           | Some (TYR_simple (_, _, i)) -> i
           | _ -> fix_module_prefix_ident org_type
       end

let type_id_to_ident_no_modify (p : Path.t id) =
  let (ns, n) = Path.to_name_list p.descr in
  let sk = ident_get_lskip p in
  Ident.mk_ident sk ns n


let type_app_to_output format p ts =
  let l = Ast.Trans (false, "type_app_to_output", None) in
  let (_, path_sep) = A.id_format_args in 
  let td = Types.type_defs_lookup l A.env.t_env p.descr in
  let sk = ident_get_lskip p in
  match Target.Targetmap.apply_target td.Types.type_target_rep A.target with
     | None -> (ts, Ident.to_output Type_ctor path_sep (type_id_to_ident p))
     | Some (TYR_simple (_, _, i)) -> (ts, ws sk ^ Ident.to_output Type_ctor path_sep i)
     | Some (TYR_subst (_, _, tnvars, t')) -> begin    
         let subst = Types.TNfmap.from_list2 tnvars ts in
         let t'' = src_type_subst subst t' in
         ([], ws sk ^ format t'')
  end

let module_id_to_ident (mod_id : Path.t id) : Ident.t =
   let l = Ast.Trans (true, "module_id_to_ident", None) in 
   let i = resolve_module_id_ident l A.env mod_id mod_id.descr in
   let i' = fix_module_ident i in
   i'

end



let component_to_output t = 
  let open Output in
    let a = Output.Target in
    match t with
      | Ast.Component_type s -> ws s ^ id a (r"type")
      | Ast.Component_field s -> ws s ^ id a (r"field")
      | Ast.Component_module s -> ws s ^ id a (r"module")
      | Ast.Component_function s -> ws s ^ id a (r"function")


