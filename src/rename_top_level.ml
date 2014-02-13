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
open Typed_ast_syntax
open Target
open Util


(* TODO: Fix this hack for recognising library functions!*)
let library_pathL : Name.t list = 
  let targetsL = List.map non_ident_target_to_mname (Targetset.elements all_targets) in
  let extraL = ["Pervasives"; "Pmap"; "Int"; "List"; "Vector"; "Set"] in
  let extranL = List.map Name.from_string extraL in
  targetsL @ extranL  

let is_lib_path path = 
  match path with 
    | [] -> true
    | p :: _ ->  List.exists (fun p' -> (Name.compare p p' = 0)) library_pathL

let prevent_lib_renames p =
  let exceptions = [] in
  let (path, n) = Path.to_name_list p in
  let path_n_s = (List.map Name.to_string path, Name.to_string n) in
  if (List.mem path_n_s exceptions) then false else is_lib_path path

(* end hack *)



let flatten_modules_macro path env ((d,s),l,lenv) =
  let l_unk = Ast.Trans(false, "flatten_modules", Some l) in
    match d with
      | Module(sk1,n,mod_path,sk2,sk3,ds,sk4) ->
          let mod_shell = ((Module(sk1,n,mod_path,sk2,sk3,[],sk4),s),l,lenv) in
          let com = ((Comment(mod_shell),None),l_unk,lenv) in
            Some((env,List.rev (com::ds)))
      | _ -> None

let flatten_modules mod_path e d = 
  let (module_path, module_name) = Path.to_name_list mod_path in
  snd (Def_trans.process_defs (List.rev module_path) flatten_modules_macro module_name e d)



let compute_ocaml_rename_constant_fun (nk : name_kind) (n : Name.t) : Name.t option =
  match nk with
    | Nk_typeconstr _ -> Name.uncapitalize n
    | Nk_const _      -> Name.uncapitalize n
    | Nk_constr _     -> Name.capitalize n
    | Nk_field _      -> Name.uncapitalize n
    | Nk_module _     -> Name.capitalize n
    | Nk_class _      -> None

let compute_isa_rename_constant_fun (nk : name_kind) (n : Name.t) : Name.t option =
  let n0 = Util.option_repeat Name.remove_underscore n in
  let n1 = Util.option_repeat Name.remove_underscore_suffix n0 in
  if (Name.compare n1 n = 0) then None else Some n1

let compute_target_rename_constant_fun (targ : Target.non_ident_target) (nk : name_kind) (n : Name.t) : Name.t option =
  match targ with 
    | Target_ocaml -> compute_ocaml_rename_constant_fun nk n 
    | Target_isa -> compute_isa_rename_constant_fun nk n 
    | _ -> None

let get_fresh_name consts consts' n = 
  let is_good n = not (NameSet.mem n consts) && not (NameSet.mem n consts') in
  if (is_good n) then None else
  Some (Name.fresh (Name.to_rope n) is_good)

let rename_constant (targ : Target.non_ident_target) (consts : NameSet.t) (consts_new : NameSet.t) (env : env) (c : const_descr_ref) : 
  (NameSet.t * env) = begin
  let l = Ast.Trans (false, "rename_constant", None) in
  let c_d = c_env_lookup l env.c_env c in
  let (is_shown, n, n_ascii_opt) = constant_descr_to_name (Target_no_ident targ) c_d in

  let compute_new_name (n : Name.t) = begin
    (* apply target specific renaming *)
    let nk = const_descr_to_kind (c, c_d) in
    let n'_opt = compute_target_rename_constant_fun targ nk n in
    let n' = Util.option_default n n'_opt in
    
    (* check whether the computed name is fresh and 
       enforce it if necessary *)
    let (is_auto_renamed, n''_opt) = 
       match get_fresh_name consts consts_new n' with
           None -> (false, n'_opt)
         | Some n'' -> (true, Some n'') in

    let n'' = Util.option_default n' n''_opt in

    let is_renamed = match n''_opt with None -> false | _ -> true in
    (is_auto_renamed, is_renamed, n'')
  end in

  let check_module_in_output () = begin
     match (Path.get_module_path c_d.const_binding) with
       | None -> true
       | Some mp -> (e_env_lookup l env.e_env mp).mod_in_output
  end in

  (* rename constant name *)
  let (consts_new, env) = if (not is_shown) then (consts_new, env) else begin
    let (is_auto_renamed, is_renamed, n_new) = compute_new_name n in

    (** add name to the list of constants to avoid *)
    let consts_new' = NameSet.add n_new consts_new  in

    if not (is_renamed) then (* do nothing *) (consts_new', env) else
    begin
      let (c_d', via_opt) = constant_descr_rename targ n_new l c_d in
      (* print warning *)
      let _ = (if (not is_auto_renamed) || not (check_module_in_output ()) then () else 
        let n_org : string = Name.to_string (Path.get_name c_d.const_binding) in
        (Reporting.report_warning env (Reporting.Warn_rename (c_d.spec_l, n_org, Util.option_map (fun (l, n) -> (Name.to_string n, l)) via_opt, Name.to_string n_new, Target_no_ident targ))))
      in
      (consts_new', env_c_env_update env c c_d')
    end
  end in

  (* rename constant ascii-name *)
  if (not is_shown) then (consts_new, env) else 
  match n_ascii_opt with None -> (consts_new, env) | Some n_ascii ->
  begin
    let (is_auto_renamed, is_renamed, n_ascii_new) = compute_new_name n_ascii in

    (** add name to the list of constants to avoid *)
    let consts_new' = NameSet.add n_ascii_new consts_new  in

    if not (is_renamed) then (* do nothing *) (consts_new', env) else
    begin
      let c_d' = {c_d with target_ascii_rep = Targetmap.insert c_d.target_ascii_rep (targ, (l, n_ascii_new))} in
      (consts_new', env_c_env_update env c c_d')
    end
  end
end

let rename_type (targ : Target.non_ident_target) (consts : NameSet.t) (consts_new : NameSet.t) (env : env) (t : Path.t) : 
  (NameSet.t * env) = begin
  let l = Ast.Trans (false, "rename_type", None) in
  let td = Types.type_defs_lookup l env.t_env t in
  let n = type_descr_to_name (Target_no_ident targ) t td in

  (* apply target specific renaming *)
  let n'_opt = compute_target_rename_constant_fun targ (Nk_typeconstr t) n in
  let n' = Util.option_default n n'_opt in
    
  (* check whether the computed name is fresh and enforce it if necessary *)
  let (is_auto_renamed, n''_opt) = 
     match get_fresh_name consts consts_new n' with
         None -> (false, n'_opt)
       | Some n'' -> (true, Some n'') in
    
  (** add name to the list of constants to avoid *)
  let n'' = Util.option_default n' n''_opt in
  let consts_new' = NameSet.add n'' consts_new  in

  match Util.option_map (fun n'' -> type_descr_rename targ n'' l td) n''_opt with
      | None -> (* if no renaming is necessary or if renaming is not possible, do nothing *) (consts_new', env)
      | Some (td', via_opt) -> begin
          (* print warning *)
          let n0 : string = Name.to_string (Path.get_name t) in
          let _ = (if (not is_auto_renamed) then () else 
                  (Reporting.report_warning env (Reporting.Warn_rename (Ast.Unknown, n0, Util.option_map (fun (l, n) -> (Name.to_string n, l)) via_opt, Name.to_string n'', Target_no_ident targ))))
          in

          (* update environment *)
          let env' = {env with t_env = Types.type_defs_update env.t_env t td'} in
          (consts_new', env')
        end
end



let rename_defs_target (targ : Target.target) ue consts env = 
  match dest_human_target targ with
    | None -> env
    | Some targ_ni ->
  begin 
    let (new_types', env) = List.fold_left (fun (consts_new, env) t -> rename_type targ_ni consts consts_new env t) (NameSet.empty, env) 
      ue.Typed_ast_syntax.used_types in


    (* rename constants *)
    let (new_consts', env) = List.fold_left (fun (consts_new, env) c -> rename_constant targ_ni consts consts_new env c) (NameSet.empty, env) 
      ue.Typed_ast_syntax.used_consts in
    env
  end


let c_env_save c_env c_id_opt c_d =
  match c_id_opt with 
    | None -> c_env_store c_env c_d
    | Some c_id -> (c_env_update c_env c_id c_d, c_id)
