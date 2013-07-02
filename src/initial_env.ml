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
open Types
open Target
open Process_file

let (^^) = Filename.concat
let r = Ulib.Text.of_latin1


(** Build type_defs for build-in types *)
let tds = 
  [(Path.listpath, mk_tc_type [Ty(Tyvar.from_rope (r"a"))] None);
   (Path.setpath, mk_tc_type [Ty(Tyvar.from_rope (r"a"))] None);
   (Path.vectorpath, mk_tc_type [Ty(Tyvar.from_rope (r"b"));Nv(Nvar.from_rope (r"a"))] None);
   (Path.numpath, mk_tc_type [] None);
   (Path.stringpath, mk_tc_type [] None);
   (Path.boolpath, mk_tc_type [] None);
   (Path.bitpath, mk_tc_type [] None);
   (Path.unitpath, mk_tc_type [] None)]

let initial_d : Types.type_defs = 
  List.fold_right (fun x y -> Types.Pfmap.insert y x) tds Types.Pfmap.empty

let initial_d = Typed_ast_syntax.type_defs_new_ident_type Ast.Unknown initial_d Path.numpath Target.Target_isa (Ident.mk_ident_strings [] "nat")

let initial_local_env : Typed_ast.local_env =
  { empty_local_env with
    p_env = Nfmap.from_list 
              [(Name.from_rope (r"bool"), (Path.boolpath, Ast.Unknown));
               (Name.from_rope (r"bit"), (Path.bitpath, Ast.Unknown));
               (Name.from_rope (r"vector"), (Path.vectorpath, Ast.Unknown));
               (Name.from_rope (r"set"), (Path.setpath, Ast.Unknown));
               (Name.from_rope (r"list"), (Path.listpath, Ast.Unknown));
               (Name.from_rope (r"string"), (Path.stringpath, Ast.Unknown));
               (Name.from_rope (r"unit"), (Path.unitpath, Ast.Unknown));
               (Name.from_rope (r"num"), (Path.numpath, Ast.Unknown))] }


let initial_env : Typed_ast.env =
  { empty_env with local_env = initial_local_env; t_env = initial_d; i_env = Pfmap.empty }

let space = Str.regexp "[ \t\n]+"

let read_constants file =
  let i = open_in file in
  let rec f () =
    try 
      let s = input_line i in
        List.map Ulib.Text.of_latin1 (Str.split space s) @ f ()
    with
      | End_of_file ->
          close_in i;
          []
  in f()

type t = 
    Typed_ast.env * (Target.target option * Ulib.Text.t list) list

let filename_to_mod file =
  Ulib.Text.of_latin1 (String.capitalize (Filename.basename (Filename.chop_extension file))) 

(* These library specifications are all built with "val" definitions, but need
 * to indicate that they are actually defined in the given target *)
let rec add_target_to_def target c_env (defs : local_env) : (c_env * local_env) =
  let (c_env', m_env') = Nfmap.fold (fun (c_env, m_env) k e -> begin
      let (c_env', mod_env') = add_target_to_def target c_env e.mod_env in
      let e' = {e with mod_env = mod_env'} in
      let m_env' = Nfmap.insert m_env (k, e') in
      (c_env', m_env') end) (c_env, Nfmap.empty) defs.m_env in

  let defs' = {defs with m_env = m_env'} in
  let c_env'' = Nfmap.fold (fun c_env k c ->
        let c_d = c_env_lookup (Ast.Trans ("add_target_to_def", None)) c_env c in
        let c_d' = match c_d.env_tag with
                    | K_val -> { c_d with env_tag = K_target(false,Targetset.singleton target) }
                    | (K_constr | K_field) -> c_d
                    | _ -> assert false
        in 
        c_env_update c_env c c_d')
        c_env' defs.v_env
  in
  (c_env'', defs')

let process_lib target file mod_name (init_env : Typed_ast.env) =
  let mp = 
    match target with
      | None -> []
      | Some(n) -> [(target_to_mname n)]
  in
  let ast = parse_file file in
  let (new_defs,_) =
    Process_file.check_ast_as_module all_targets mp init_env mod_name ast
  in
  let new_defs2 =
    match target with
      | None -> new_defs
      | Some(tgt) -> 
        let (c_env', local_env') = add_target_to_def tgt new_defs.c_env new_defs.local_env in
        {new_defs with c_env = c_env'; local_env = local_env'}
  in
    (new_defs2)

let add_lib (e1 : local_env) (e2 : env) = {e2 with local_env = local_env_union e2.local_env e1 }

let add_open_lib k e1 e2 =
  match Nfmap.apply e2.local_env.m_env (Name.from_rope k) with
    | Some e ->
        {e2 with local_env = local_env_union (local_env_union e1 e2.local_env) e.mod_env }
    | None ->
        assert false

(* Process a library for the given target and open it in the current init_env *)
let proc_open target file env =
  let mod_name = filename_to_mod file in
  let new_env = process_lib target file mod_name env in
    (add_open_lib mod_name env.local_env new_env)

(* Process a library for the given target *)
let proc target file env =
  let mod_name = filename_to_mod file in
  let new_env = process_lib target file mod_name env in
    (add_lib env.local_env new_env)

(* TODO: Add to the constants *)
let add_to_init targ file (((env:env), consts):t) : t =
  let targ_env = 
    match Nfmap.apply env.local_env.m_env (target_to_mname targ) with 
      | Some(e) -> e
      | None -> assert false
  in
  let p = 
    match targ with
      | Target_ocaml -> proc
      | Target_isa -> proc_open
      | Target_coq -> proc
      | Target_hol -> proc_open
      | Target_tex -> assert false
      | Target_html -> assert false
  in
  let new_env = p (Some targ) file {env with local_env = targ_env.mod_env} in
    ({ new_env with local_env = {env.local_env with m_env = Nfmap.insert new_env.local_env.m_env (target_to_mname targ, {targ_env with mod_env = new_env.local_env})}}, 
     consts)

module Initial_libs (P : sig val path : string end) =
struct
  open P

  let full_filename targ f = 
    List.fold_right Filename.concat [path; target_to_string targ] (f ^ ".lem")
  ;;

  (* HOL Env *)
  let hol_env = 
    List.fold_left
      (fun init_env t -> proc_open (Some(Target_hol)) (full_filename Target_hol t) init_env)
      initial_env
      ["min"; "bool"; "pair"; "arithmetic"; "pred_set"; "finite_map"; "list"; "string"; "sorting"; "set_relation"; "fixedPoint"; "integer"]

  let hol_env' = env_m_env_move hol_env (target_to_mname Target_hol) initial_local_env


  (* Coq Env *)
  let coq_perv = proc_open (Some Target_coq) (full_filename Target_coq "pervasives") hol_env';;

  let coq_env = 
    List.fold_left (
      fun init_env t ->
        proc (Some Target_coq) (full_filename Target_coq t) init_env
    ) coq_perv
    ["pervasives"; "set"; "list"] 
  ;;
  
  let coq_env' = env_m_env_move coq_env (target_to_mname Target_coq) initial_local_env
  let hol_env' = {coq_env' with local_env = hol_env'.local_env}

  (* OCAML Env *)
  let ocaml_perv = proc_open (Some(Target_ocaml)) (full_filename Target_ocaml "pervasives") hol_env'

  let ocaml_env = 
    List.fold_left
      (fun init_env t -> proc (Some(Target_ocaml)) (full_filename Target_ocaml t) init_env)
      ocaml_perv
      ["list"; "pset"; "pmap"; "nat_num" ; "vector" ; "bit"]
  
  let ocaml_env' = env_m_env_move ocaml_env (target_to_mname Target_ocaml) initial_local_env
  let hol_env' = {ocaml_env' with local_env = hol_env'.local_env}

  (* Isabelle Env *)
  let isa_perv = proc_open (Some(Target_isa)) (full_filename Target_isa "pervasives") hol_env'

  let isa_env = 
      List.fold_left
        (fun init_env t -> proc_open (Some(Target_isa)) (full_filename Target_isa t) init_env)
        isa_perv
        ["pervasives";"list";"set";"finite_Set";"map"]   
        (* PS HACK - TEMPORARILY REMOVE IN HOPES OF GETTING HOL BUILD *)
  
  let isa_env' = env_m_env_move isa_env (target_to_mname Target_isa) initial_local_env

  let env = {isa_env' with local_env = 
     local_env_union hol_env'.local_env (
     local_env_union coq_env'.local_env (
     local_env_union isa_env'.local_env 
                     ocaml_env'.local_env)) }
     
  let perv =
    proc_open None (Filename.concat path "pervasives.lem") env
  ;;

  let env =
     List.fold_left (
       fun env t -> proc None (Filename.concat path (t ^ ".lem")) env
     ) perv ["list"; "set"; "pmap"; "int" ; "vector" ; "bit"];;

  let env = set_target_const_rep env ["Pervasives"] "SUC" Target_isa (CR_new_ident (Ast.Unknown, false, Ident.mk_ident_strings [] "Suc"));;
  let env = set_target_const_rep env ["Pervasives"] "SUC" Target_hol (CR_new_ident (Ast.Unknown, false, Ident.mk_ident_strings [] "SUC"));;

  let init =
    (env,
     [(Some(Target_hol),
       read_constants (path ^^ target_to_string Target_hol ^^ "constants"));
      (Some(Target_isa),
       read_constants (path ^^ target_to_string Target_isa ^^ "constants"));
      (Some(Target_ocaml),
       []);
      (Some(Target_coq),
       read_constants (path ^^ target_to_string Target_coq ^^ "constants"));
      (None,
       []);
      (Some(Target_tex),
       []);
      (Some(Target_html),
       [])])
end
