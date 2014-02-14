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


let def_add_location_comment_flag = ref false

let def_add_location_comment (((d,s),l,lenv) : def) =
  if not (!def_add_location_comment_flag) then (emp, d) else
  begin
    let (((d', _), _, _), sk) = def_alter_init_lskips (fun sk -> (None, sk)) ((d,s),l,lenv) in
    let c = String.concat "" [" "; Reporting_basic.loc_to_string true l; " "] in
    let out_before = ws sk ^ comment c ^ new_line in
    (out_before, d')
  end

(* Resolve a const identifier stored inside a id, with a full one in case of Id_none *)
let resolve_constant_id_ident l env targ id : Ident.t =
  resolve_const_ref l env targ id.id_path id.descr

let resolve_type_id_ident l env id path : Ident.t =
  resolve_type_path l env id.id_path path

let resolve_module_id_ident l env id path : Ident.t =
  resolve_module_path l env id.id_path path

let cr_special_uncurry_fun n arg_f name vars argsL = begin
  if not (List.length argsL = n) then
     raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal (Ast.Unknown, "target presentation of OCaml constructor got the wrong number of args")))
  else if (n = 0) then [name] else
  if (n = 1) then
     [name; texspace; arg_f (List.nth argsL 0)]
  else
     [name; texspace; meta "("] @
      Util.intercalate (meta ",") (List.map arg_f argsL) @
     [meta ")"]
  end

(** Axiliary function for [inline_exp] and [cr_special_rep_fun] *)
let rec build_subst (params : name_lskips_annot list) (args : exp list) 
      : exp_subst Nfmap.t * name_lskips_annot list * exp list =
  match (params, args) with
    | ([],args) -> (Nfmap.empty, [], args)
    | (params, []) -> (Nfmap.empty, params, [])
    | (p::params, a::args) ->
        let (subst, x, y) = build_subst params args in
        let (a', _) = alter_init_lskips remove_init_ws a in
          (Nfmap.insert subst (Name.strip_lskip p.term, Sub(a')), x, y)


let cr_special_rep_fun srepl rep_args env tsubst arg_f name vars (vargsL : exp list) = begin
  let _ = if ((List.length vargsL = List.length vars) &&
              (List.length srepl = List.length rep_args + 1)) then () else 
     raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal (Ast.Unknown, 
       "special target presentation of OCaml got wrong numer of args")))
  in 
  let module C = Exps_in_context(struct let env_opt = Some env;; let avoid = None end) in
  let (vsubst, _, _) = build_subst vars vargsL in
  let rep_args' = List.map (C.exp_subst (tsubst,vsubst)) rep_args in

  let args_o = List.map (fun a -> Output.remove_initial_ws (arg_f a)) rep_args' in
  let srepl_o = List.map meta srepl in

  Util.interleave srepl_o args_o
end


let cr_special_fun_to_fun_pat err = function
  | CR_special_uncurry n -> cr_special_uncurry_fun n
  | CR_special_rep _ -> err ()

let cr_special_fun_to_fun_exp env tsubst = function
  | CR_special_uncurry n -> cr_special_uncurry_fun n
  | CR_special_rep (srepl, exps) -> cr_special_rep_fun srepl exps env tsubst 


let inline_exp l (target : Target.target) env was_infix params body_sk body tsubst (args : exp list) : exp =
  let module C = Exps_in_context(struct let env_opt = Some env;; let avoid = None end) in
  let loc = Ast.Trans(false, "inline_exp", Some l) in
  let (vsubst, leftover_params, leftover_args) = build_subst params args in

  (* adapt whitespace before body *)
  let b = body in
  let b = (fst (alter_init_lskips (fun _ -> (body_sk, None)) b)) in
  let b = C.exp_subst (tsubst,vsubst) b in
  let stays_infix = Precedence.is_infix (Precedence.get_prec_exp target env b) in
  if params = [] && was_infix && stays_infix then
  begin
    (* Turn infix operators into infix operators again *)
    match leftover_args with
      | [a1; a2] -> C.mk_infix loc a1 b a2 None
      | _ -> raise (Reporting_basic.err_unreachable l "infix operator with not 2 arguments")
  end else 
  if leftover_params = [] then
    let res = (* all parameters are instantiatated *)
    (List.fold_left 
       (fun e e' -> C.mk_app loc e e' None)
       b
       leftover_args) in
    (* was b something lengthy or fancy, while before we had a single function? Then add parens *)
    if (may_need_paren b && params = []) then mk_opt_paren_exp res else res
  else
    (* begin get rid of the space in front of b and move it to the beginning *)
    let (b, b_sk) = alter_init_lskips (fun sk -> (None, sk)) b in
    append_lskips b_sk (mk_opt_paren_exp (C.mk_fun loc None
         (List.map (fun n -> C.mk_pvar n.locn n.term (Types.type_subst tsubst n.typ))
                                  leftover_params) 
         None b None))


let generalised_inline_exp_macro (do_CR_simple : bool) (target : Target.target) env e =
  let l_unk = Ast.Trans(false, "inline_exp_macro", Some (exp_to_locn e)) in
  let module C = Exps_in_context(struct let env_opt = Some env;; let avoid = None end) in
  let (f,args,was_infix) = strip_app_infix_exp e in
    match C.exp_to_term f with
      | Constant(c_id) ->
          let cd = c_env_lookup l_unk env.c_env c_id.descr in
          let do_it (params, body) : exp =
            let tsubst = Types.TNfmap.from_list2 cd.const_tparams c_id.instantiation in
            inline_exp l_unk target env was_infix params (ident_get_lskip c_id) body tsubst args
          in

          let subst_opt = begin            
            match Target.Targetmap.apply_target cd.target_rep target with
              | Some(CR_inline (_, _, params,body)) -> Some (params, body)
              | Some(CR_simple (_, _, params,body)) when do_CR_simple -> Some (params, body)
              | _ -> None
          end in
          Util.option_map do_it subst_opt
      | _ -> None


let inline_exp_macro (target : Target.non_ident_target) env _ e =
  generalised_inline_exp_macro false (Target.Target_no_ident target) env e


let inline_pat_err l c_path target cr_l =
  let m = String.concat "" ["constant "; Path.to_string (c_path);
                            " cannot be used in a pattern.\n  It as has too complicated ";
                            "target representation for target "; Target.target_to_string target;
                            ".\n  This is defined at\n    ";
                            (Reporting_basic.loc_to_string true cr_l)] in
  raise (Reporting_basic.Fatal_error (Reporting_basic.Err_fancy_pattern_constant (l, m)))


let inline_pat l_unk env cd c_id ps (params, body) =
   let module C = Exps_in_context(struct let env_opt = Some env;; let avoid = None end) in
   let tsubst = Types.TNfmap.from_list2 cd.const_tparams c_id.instantiation in
   
   (* adapt whitespace before body *)
   let b = (fst (alter_init_lskips (fun _ -> (ident_get_lskip c_id, None)) body)) in
   let b = C.exp_subst (tsubst,Nfmap.empty) b in
            
   match (params, C.exp_to_term b) with
     | ([], Constant c_id') -> Some (C.mk_pconst l_unk c_id' ps None)
     | ([], Backend (sk, i)) -> 
          let ty = Types.type_subst tsubst cd.const_type in
          Some (C.mk_pbackend l_unk sk i ty ps None)
     | _ -> None


let generalised_inline_pat_macro (do_CR_simple : bool) (target : Target.target) env p =
  let l_unk = Ast.Trans(false, "inline_pat_macro", Some p.locn) in
    match p.term with
      | P_const(c_id, ps) ->
          if (Pattern_syntax.is_not_buildin_constructor l_unk env target c_id.descr) then 
            (* let pattern matching handle constructors *) None 
          else begin
            let cd = c_env_lookup l_unk env.c_env c_id.descr in
            let res_opt = begin            
              match Target.Targetmap.apply_target cd.target_rep target with
                | Some(CR_inline (l, _, params,body)) -> (Some l, inline_pat l_unk env cd c_id ps (params, body))
                | Some(CR_simple (l, _, params,body)) -> 
                  if do_CR_simple then
                    (Some l, inline_pat l_unk env cd c_id ps (params, body))
                  else
                    (None, None)
                | _ -> (None, None)
            end in begin
              match res_opt with
                | (_,  Some p) -> Some p
                | (None, None) -> None
                | (Some l, None) -> inline_pat_err p.locn cd.const_binding target l
            end
          end
      | _ -> None


let inline_pat_macro (target : Target.non_ident_target) env _ _ p =
  generalised_inline_pat_macro false (Target.Target_no_ident target) env p


let get_module_name_from_descr md mod_name extra_rename target = begin
  let transform_name_for_target n = match target with
    | Target.Target_no_ident (Target.Target_coq) -> Util.uncapitalize_prefix n
    | Target.Target_no_ident (Target.Target_hol) -> Util.string_map (fun c -> if c = '-' then  '_' else c) (Util.uncapitalize_prefix n)
    | _ -> n
  in
  let lem_mod_name = match Target.Targetmap.apply_target md.mod_target_rep target with
    | Some (MR_rename (_, n)) -> n
    | _ -> mod_name
  in
  extra_rename (transform_name_for_target (Name.to_string lem_mod_name))
end

let get_module_name env target path mod_name =  begin
  let md = lookup_mod_descr env path mod_name in
  Name.from_string (get_module_name_from_descr md mod_name (fun s -> s) target)
end

let isa_add_full_library_path_flag = ref false 

let adapt_isabelle_library_dir dir =
  if (Util.dir_eq (Filename.concat Build_directory.d "library") dir) then
     (if (!isa_add_full_library_path_flag) then (Filename.concat Build_directory.d "isabelle-lib") else "")
  else 
     dir


(* this function modifies target specific imports. It's main purpose is to replace
   variables in these imports. "$LIB_DIR/" gets replaced with either "" if we are
   outputting in the library-directory or the full path to it otherwise. *)
let get_module_open_string_target =
 let abs_lib_dir = Util.option_default Filename.current_dir_name 
   (Util.absolute_dir (Filename.concat Build_directory.d "isabelle-lib")) in

 fun target dir mod_string ->
 match target with
    | Target.Target_no_ident (Target.Target_isa) -> 
        let new_dir = if (not (!isa_add_full_library_path_flag)) then "" else
          (if Util.dir_eq dir abs_lib_dir then "" else (String.concat "" [abs_lib_dir; "/"])) in
        Str.global_replace (Str.regexp_string "$LIB_DIR/") new_dir mod_string 
    | _ -> mod_string


let get_module_open_string env target dir mod_path =
begin
  let transform_name md mod_string = match target with
    | Target.Target_no_ident (Target.Target_hol) -> String.concat "" [mod_string; "Theory"]
    | Target.Target_no_ident (Target.Target_isa) -> begin
        match md.mod_filename with
          | None -> mod_string
          | Some fn -> begin
              let mod_dir_opt = Util.absolute_dir (adapt_isabelle_library_dir (Filename.dirname fn)) in
              let out_dir_opt = Util.absolute_dir dir in
              match (mod_dir_opt, out_dir_opt) with
                | (Some mod_dir, Some out_dir) ->
                     if (String.compare mod_dir out_dir = 0) then
                       mod_string 
                     else
                       Filename.concat mod_dir mod_string
                | _ -> mod_string
            end
      end 
    | _ -> mod_string
  in
  let md = e_env_lookup Ast.Unknown env.e_env mod_path in
  get_module_name_from_descr md (Path.get_name mod_path) (transform_name md) target
end


let rec concat_skip_lists acc sk = function
  | [] -> (List.rev acc, sk)
  | (sk', sl) :: skip_list -> begin
      let sl' = List.filter (fun s -> not (List.exists (fun (_, s') -> s = s') acc)) sl in
      match sl' with
        | [] -> concat_skip_lists acc (Ast.combine_lex_skips sk sk') skip_list
        | (s :: sl) -> 
             let acc = List.rev_append (List.map (fun s -> (space, s)) sl) ((Ast.combine_lex_skips sk sk', s) :: acc) in
             concat_skip_lists acc None skip_list
    end 

let imported_module_to_strings env target dir = function
  | IM_paths ids -> List.map (get_module_open_string env target dir) ids
  | IM_targets (targs, strings) -> 
      if (Typed_ast.in_targets_opt target targs) then List.map (get_module_open_string_target target dir) strings else []

let get_imported_target_modules_of_def_aux = function
  | OpenImport ((Ast.OI_import _ | Ast.OI_open_import _ | Ast.OI_include_import _), ids) ->      
      Some (IM_paths (List.map (fun id -> id.descr) ids))
  | OpenImportTarget ((Ast.OI_import _ | Ast.OI_open_import _ | Ast.OI_include_import _), targs, ts) ->      
      Some (IM_targets (targs, (List.map snd ts)))
  | _ -> None

let get_imported_target_modules ((ds, _) : Typed_ast.def list * Ast.lex_skips)  =
  Util.map_filter (fun ((d, _), _, _) -> get_imported_target_modules_of_def_aux d) ds 

let imported_modules_to_strings env target dir iml =
  Util.remove_duplicates (List.flatten (List.map (imported_module_to_strings env target dir) iml));;

module Make(A : sig 
  val env : env;; 
  val target : Target.target;;
  val dir : string;;
  val id_format_args : (bool -> Output.id_annot -> Ulib.Text.t -> Output.t) * Ulib.Text.t
 end) = struct


let open_to_open_target ms =
begin
  let sk_sl_list = List.map (fun id -> (ident_get_lskip id, [get_module_open_string A.env A.target A.dir id.descr])) ms in
  concat_skip_lists [] None sk_sl_list
end

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

let ident_to_output use_infix from_backend =
  let (ident_f, sep) = A.id_format_args in 
  Ident.to_output_format (ident_f use_infix) (Term_const (false, from_backend)) sep


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
  let l = Ast.Trans (false, "const_id_to_ident", (Some c_id.id_locn)) in
  let c_descr = c_env_lookup l A.env.c_env c_id.descr in
  let org_ident = resolve_constant_id_ident l A.env A.target c_id in
  let (_, n, n_ascii_opt) = constant_descr_to_name A.target c_descr in
  let (ascii_used, given_used, ident')  =    
    match (n_ascii_opt, ascii_alternative, given_id_opt) with
      | (Some ascii, true, _) -> (true, false, Ident.rename org_ident ascii)
      | (_, false, Some i) -> (false, true, Ident.replace_lskip i (Ident.get_lskip org_ident))
      | _  -> (false, false, Ident.rename org_ident n)
  in
  let ident = fix_module_prefix_ident ident' in
  (ascii_used, given_used, ident)
;;

let const_id_to_ident c_id ascii_alternative = (let (_, _, i) = const_id_to_ident_aux c_id ascii_alternative None in i)

let constant_application_to_output_simple is_infix_pos arg_f alter_sk_f args c_id ascii_alternative given_id_opt = begin
  let (ascii_used, given_id_used, i) = const_id_to_ident_aux c_id ascii_alternative given_id_opt in 
  let const_is_infix = not (ascii_used) && Precedence.is_infix (Precedence.get_prec A.target A.env c_id.descr) in 
  let const_is_infix_input = Precedence.is_infix (Precedence.get_prec Target.Target_ident A.env c_id.descr) in
  let is_infix = (const_is_infix && (Ident.has_empty_path_prefix i) && (List.length args = 2) &&
                  (is_infix_pos || not const_is_infix_input)) in           
  let use_infix_notation = ((not is_infix) && const_is_infix) in

  (* adapt whitespace *)
  let (i, args) = if (is_infix && not is_infix_pos) || (not is_infix && is_infix_pos) then
      begin (* print "f arg1 arg2" as "arg1 f arg2" or vise versa, so swap space of arg1 and f *)
        match args with
          | [arg1; arg2] -> 
              let (arg1', arg1_sk) = alter_sk_f (fun sk -> (Ident.get_lskip i, sk)) arg1 in
              let i' = Ident.replace_lskip i arg1_sk in
              (i', [arg1'; arg2])
          | _ -> (i, args)
      end
    else (i, args)
  in
  let name = ident_to_output use_infix_notation given_id_used i in
  let args_out = List.map (arg_f use_infix_notation) args in

  if (not is_infix) then
     (name :: args_out) 
  else 
     [(List.nth args_out 0); name; (List.nth args_out 1)]
end

(* assumes that there are enough arguments, otherwise list_split_after will fail *)
let constant_application_to_output_special c_id to_out cr_to_fun arg_f args vars : Output.t list =
  let i = const_id_to_ident c_id false in
  let name = ident_to_output false false i in
  let (a_vars, a_rest) = Util.split_after (List.length vars) args (* assume there are enough elements, because of call discipline *) in
  let o_fun = (cr_to_fun to_out) arg_f name vars a_vars in
  o_fun @ List.map arg_f a_rest



let function_application_to_output l (arg_f0 : exp -> Output.t) (is_infix_pos : bool) (full_exp : exp) (c_id : const_descr_ref id) (args : exp list) (ascii_alternative: bool) : Output.t list =
  let _ = if is_infix_pos && not (List.length args = 2) then (raise (Reporting_basic.err_unreachable l "Infix position with wrong number of args")) else () in
  let arg_f b e = if b then arg_f0 (mk_opt_paren_exp e) else arg_f0 e in
  let c_descr = c_env_lookup Ast.Unknown A.env.c_env c_id.descr in
  match Target.Targetmap.apply_target c_descr.target_rep A.target with
     | Some (CR_special (_, _, to_out, vars)) when not ascii_alternative -> 
            if (List.length args < List.length vars) then begin
              (* eta expand and call recursively *)
              let remaining_vars = List.map (fun n -> Name.strip_lskip n.term) (Util.list_dropn (List.length args) vars) in
              let eta_exp = mk_eta_expansion_exp (A.env.t_env) remaining_vars full_exp in
              [arg_f true eta_exp]
              
            end else begin
              let tsubst = Types.TNfmap.from_list2 c_descr.const_tparams c_id.instantiation in
              constant_application_to_output_special c_id to_out (cr_special_fun_to_fun_exp A.env tsubst) (arg_f false) args vars 
            end
     | Some (CR_simple (_, _, params,body)) when not ascii_alternative -> begin
         let tsubst = Types.TNfmap.from_list2 c_descr.const_tparams c_id.instantiation in
         let new_exp = inline_exp l A.target A.env is_infix_pos params (ident_get_lskip c_id) body tsubst args in
         [arg_f false new_exp]
       end
     | Some (CR_infix (_, _, _, i)) -> constant_application_to_output_simple is_infix_pos arg_f alter_init_lskips args c_id ascii_alternative (Some i)
     | Some (CR_undefined (l', _)) -> 
       begin 
         let (^) = Pervasives.(^) in
         let m0 = "constant '" ^ Path.to_string c_descr.const_binding ^ "' is explicitly declared undefined for target " ^ (Target.target_to_string A.target) ^ " at\n    " in
         let loc_s = Reporting_basic.loc_to_string false l' in 
         raise (Reporting_basic.Fatal_error (Reporting_basic.Err_type (l, 
           (m0 ^ loc_s))))
       end
     | _ -> constant_application_to_output_simple is_infix_pos arg_f alter_init_lskips args c_id ascii_alternative None

let pattern_application_to_output l (arg_f0 : pat -> Output.t) (c_id : const_descr_ref id) (args : pat list) (ascii_alternative : bool) : Output.t list =
  let arg_f b p = if b then arg_f0 (Pattern_syntax.mk_opt_paren_pat p) else arg_f0 p in
  let c_descr = c_env_lookup Ast.Unknown A.env.c_env c_id.descr in
  match Target.Targetmap.apply_target c_descr.target_rep A.target with
     | Some (CR_special (_, _, to_out, vars)) when not ascii_alternative -> 
        if (List.length args < List.length vars) then begin
           raise (Reporting_basic.err_unreachable Ast.Unknown "Constructor without enough arguments!")
        end else begin
           constant_application_to_output_special c_id to_out 
             (cr_special_fun_to_fun_pat (fun () -> inline_pat_err Ast.Unknown c_descr.const_binding A.target l)) 
             (arg_f false) args vars 
        end
     | Some (CR_simple (l, _, params,body)) when not ascii_alternative -> begin
         let res_opt = inline_pat Ast.Unknown A.env c_descr c_id args (params, body) in
         match res_opt with
           | None -> inline_pat_err Ast.Unknown c_descr.const_binding A.target l 
           | Some p' -> [arg_f false p']
       end
     | Some (CR_undefined (l', _)) -> 
       begin 
         let (^) = Pervasives.(^) in
         let m0 = "constant '" ^ Path.to_string c_descr.const_binding ^ "' is explicitly declared undefined for target " ^ (Target.target_to_string A.target) ^ " at\n    " in
         let loc_s = Reporting_basic.loc_to_string false l' in 
         raise (Reporting_basic.Fatal_error (Reporting_basic.Err_type (l, 
           (m0 ^ loc_s))))
       end
     | _ -> constant_application_to_output_simple false arg_f pat_alter_init_lskips args c_id ascii_alternative None

let type_path_to_name n0 (p : Path.t) : Name.lskips_t =
  let l = Ast.Trans (false, "type_path_to_name", None) in
  let td = Types.type_defs_lookup l A.env.t_env p in
  let n = type_descr_to_name A.target p td in
  let n' = Name.replace_lskip (Name.add_lskip n) (Name.get_lskip n0) in
  n'

let type_id_to_ident_aux (p : Path.t id) =
   let l = Ast.Trans (false, "type_id_to_ident", None) in
   let td = Types.type_defs_lookup l A.env.t_env p.descr in
   let org_type = resolve_type_id_ident l A.env p p.descr in
   match Target.Targetmap.apply_target td.Types.type_rename A.target with
     | Some (_, n) -> (false, fix_module_prefix_ident (Ident.rename org_type n))
     | None -> begin
         match Target.Targetmap.apply_target td.Types.type_target_rep A.target with
           | Some (TYR_simple (_, _, i)) -> (true, Ident.replace_lskip i (Ident.get_lskip org_type))
           | _ -> (false, fix_module_prefix_ident org_type)
       end

let type_id_to_ident (p : Path.t id) = snd (type_id_to_ident_aux p)

let type_id_to_output (p : Path.t id) =
  let (needs_no_escape, i) = type_id_to_ident_aux p in
  let (_, path_sep) = A.id_format_args in 
  Ident.to_output (Type_ctor (false, not needs_no_escape)) path_sep i

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
     | None -> (ts, Ident.to_output (Type_ctor (false, false)) path_sep (type_id_to_ident p))
     | Some (TYR_simple (_, _, i)) -> (ts, ws sk ^ Ident.to_output (Type_ctor (false, true)) path_sep i)
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
    let a = Output.Component in
    match t with
      | Ast.Component_type s -> ws s ^ id a (r"type")
      | Ast.Component_field s -> ws s ^ id a (r"field")
      | Ast.Component_module s -> ws s ^ id a (r"module")
      | Ast.Component_function s -> ws s ^ id a (r"function")


