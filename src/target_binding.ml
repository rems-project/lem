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
   [minimize_module_prefix eq_fun env [m1, ... , mn]] tries minimize the module prefix
   needed to describe [name]. It is first checked, whether [name] means the same as the full
   prefixed version in [env]. If this is not the case, the function tries to chop of 
   module names at the beginning, as long as the meaning in [env] is preserved. In order to check
   whether it "means" the same, the function [eq_fun] is applied to the local environments reachable from [env]
   with the different module prefixes.

   (* TODO: perhaps performance improvements *)
 *)

let minimize_module_prefix (eq_fun : local_env -> local_env -> bool) (env : local_env) (p : Name.t list) : Name.t list =
begin 
  let p_env = lookup_env env p in

  let compare_prefix p2 = begin
    let p2_env_opt = lookup_env_opt env p2 in

    match p2_env_opt with
      | (Some p2_env) -> eq_fun p_env p2_env
      | _ -> false
  end in

  (* let's try to drop p completely *)
  let drop_all = match p with | []  -> true | _ -> compare_prefix [] in
  if drop_all then [] else
  begin
    let rec aux = function
      | [] -> []
      | [m] -> (* drop all already tested *) [m]
      | m1 :: m2 :: ms -> if compare_prefix (m2 :: ms) then
                             aux (m2 :: ms) else (m1 :: m2 :: ms)
    in
      aux p
  end
end;;

let minimize_module_path env (p : Path.t) =
  let (ns, n) = Path.to_name_list p in
  let mod_eq env1 env2 = begin
    let md1_opt = lookup_mod_descr_opt env1 [] n in
    let md2_opt = lookup_mod_descr_opt env2 [] n in
    match (md1_opt, md2_opt) with
      | (Some md1, Some md2) -> (Path.compare md1.mod_binding md2.mod_binding = 0)
      | _ -> false
  end in
  let ns' = minimize_module_prefix mod_eq env ns in
  Path.mk_path ns' n

let minimize_const_ident env (i : Ident.t) =
  let (ns, n) = Ident.to_name_list i in
  let const_eq env1 env2 = begin
    let c1_opt = Nfmap.apply env1.v_env n in
    let c2_opt = Nfmap.apply env2.v_env n in
    match (c1_opt, c2_opt) with
      | (Some c1, Some c2) -> (c1 = c2)
      | _ -> false
  end in
  let ns' = minimize_module_prefix const_eq env ns in
  Ident.mk_ident (Ident.get_first_lskip i) ns' n

let minimize_type_ident env (i : Ident.t) =
  let (ns, n) = Ident.to_name_list i in
  let type_eq env1 env2 = begin
    let t1_opt = Nfmap.apply env1.p_env n in
    let t2_opt = Nfmap.apply env2.p_env n in
    match (t1_opt, t2_opt) with
      | (Some (t1, _), Some (t2, _)) -> (Path.compare t1 t2 = 0)
      | _ -> false
  end in
  let ns' = minimize_module_prefix type_eq env ns in
  Ident.mk_ident (Ident.get_first_lskip i) ns' n
