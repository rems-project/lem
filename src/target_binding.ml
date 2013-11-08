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

open Typed_ast
open Typed_ast_syntax


(* Given some entity of the form [m1. ... . mn . name] the function 
   [search_module_suffix eq_fun env [m1, ... , mn]] finds the minimum module prefix
   needed to describe [name]. The function [is_ok] must return [true] if the
   entity can be found in the local environment of a given module.
 *)
let search_module_suffix (env : Typed_ast.env) (is_ok : Typed_ast.env -> bool) (default : Name.t list option) (ns : Name.t list) = 
  let suffix_ok ns =
    let env_opt = lookup_env_opt env ns in
    match env_opt with
      | Some lenv -> is_ok {env with local_env = lenv}
      | _ -> false
  in
  let rec aux acc ns = 
    let acc = if suffix_ok ns then Some ns else acc in
    match ns with
      | [] -> acc
      | n::ns -> aux acc ns
  in
  match default with
    | Some dns -> if suffix_ok dns then Some dns else aux None ns
    | _ -> aux None ns


let resolve_module_path l env i_opt (p : Path.t) =
  let (ns, n) = Path.to_name_list p in
  let (default_ns, sk) = match i_opt with
    | Types.Id_none sk -> (None, sk)
    | Types.Id_some i -> (Some (fst (Ident.to_name_list i)), Ident.get_lskip i) in
  let is_ok lenv =
    let md_opt = lookup_mod_descr_opt lenv [] n in
    match md_opt with
      | None -> false
      | Some md -> Path.compare md.mod_binding p  = 0
  in
  match search_module_suffix env is_ok default_ns ns with
    | Some ns' -> Ident.mk_ident sk ns' n
    | None ->
      raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal
          (l, "could not resolve module path " ^ Path.to_string p))) 

let resolve_type_path l env i_opt p = 
  let (ns, n) = Path.to_name_list p in
  let (default_ns, sk) = match i_opt with
    | Types.Id_none sk -> (None, sk)
    | Types.Id_some i -> (Some (fst (Ident.to_name_list i)), Ident.get_lskip i) in
  let is_ok env =
    let p_opt = Nfmap.apply env.local_env.p_env n in
    match p_opt with
      | None -> false
      | Some (p',_) -> Path.compare p p' = 0
  in
  match search_module_suffix env is_ok default_ns ns with
    | Some ns' -> Ident.mk_ident sk ns' n
    | None ->
      raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal
          (l, "could not resolve type path " ^ Path.to_string p))) 

let resolve_const_ref l env targ i_opt c_ref = 
  let c_descr = c_env_lookup Ast.Unknown env.c_env c_ref in
  let c_kind = const_descr_to_kind (c_ref, c_descr) in
  let (ns, n) = Path.to_name_list c_descr.const_binding in
  let (default_ns, sk) = match i_opt with
    | Types.Id_none sk -> (None, sk)
    | Types.Id_some i -> (Some (fst (Ident.to_name_list i)), Ident.get_lskip i) in  
  let is_ok env = 
    let lenv = env.local_env in
    let m = match c_kind with
              | Nk_field _ -> lenv.f_env 
              | _ -> lenv.v_env
    in
    let c_ref_opt = Nfmap.apply m n in
    match c_ref_opt with
      | None -> false
      | Some c_ref' -> ((c_ref = c_ref') ||
        begin
          let c_descr' = c_env_lookup Ast.Unknown env.c_env c_ref' in
          (Path.compare c_descr.const_binding c_descr'.const_binding = 0)
(* TODO: figure out why the following is is not working / bug in dictionary passing ?
   Target.Targetmap.apply_target c_descr'.const_no_class targ = Some c_ref *)
        end)
  in
  match search_module_suffix env is_ok default_ns ns with
    | Some ns' -> Ident.mk_ident sk ns' n
    | None -> let m = String.concat "\n    "  [
        "could not resolve constant path " ^ Path.to_string c_descr.const_binding;
        "This is usally caused by using transformations like inlining, target representations or special pattern matching";
        "to introduce a contant in code, where it is not defined yet."] in
      raise (Reporting_basic.Fatal_error (Reporting_basic.Err_internal
          (l, m)))









