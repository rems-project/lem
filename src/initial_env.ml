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
open Types
open Process_file

let (^^) = Filename.concat
let r = Ulib.Text.of_latin1

let tds = 
  [(Path.listpath, Tc_type([Ty(Tyvar.from_rope (r"a"))], None, None));
   (Path.setpath, Tc_type([Ty(Tyvar.from_rope (r"a"))], None, None));
   (Path.vectorpath, Tc_type([Ty(Tyvar.from_rope (r"b"));Nv(Nvar.from_rope (r"a"))], None, None));
   (Path.numpath, Tc_type([], None, None));
   (Path.stringpath, Tc_type([], None, None));
   (Path.boolpath, Tc_type([], None, None));
   (Path.bitpath, Tc_type([], None, None));
   (Path.unitpath, Tc_type([],None, None))]

let initial_d : Types.type_defs = 
  List.fold_right (fun x y -> Types.Pfmap.insert y x) tds Types.Pfmap.empty

let initial_env : Typed_ast.env =
  { m_env = Nfmap.empty;
    v_env = Nfmap.empty;
    f_env = Nfmap.empty;
    p_env = Nfmap.from_list 
              [(Name.from_rope (r"bool"), (Path.boolpath, Ast.Unknown));
               (Name.from_rope (r"bit"), (Path.bitpath, Ast.Unknown));
               (Name.from_rope (r"vector"), (Path.vectorpath, Ast.Unknown));
               (Name.from_rope (r"set"), (Path.setpath, Ast.Unknown));
               (Name.from_rope (r"list"), (Path.listpath, Ast.Unknown));
               (Name.from_rope (r"string"), (Path.stringpath, Ast.Unknown));
               (Name.from_rope (r"unit"), (Path.unitpath, Ast.Unknown));
               (Name.from_rope (r"num"), (Path.numpath, Ast.Unknown))] }

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
    ((type_defs * instance list Pfmap.t) * Typed_ast.env) *
    (Typed_ast.target option * Ulib.Text.t list) list

let filename_to_mod file =
  Ulib.Text.of_latin1 (String.capitalize (Filename.basename (Filename.chop_extension file))) 

(* These library specifications are all built with "val" definitions, but need
 * to indicate that they are actually defined in the given target *)
let rec add_target_to_def target defs =
  { defs with 
        m_env = Nfmap.map (fun k e -> { e with mod_env = add_target_to_def target e.mod_env}) defs.m_env;
        v_env = 
          Nfmap.map 
            (fun k v -> 
               match v with 
                 | Constr _ -> v
                 | Val(c) -> 
                     assert (c.env_tag = K_val);
                     Val ({ c with env_tag = K_target(false,Targetset.singleton target) }))
            defs.v_env }

let process_lib target file mod_name init_env =
  let mp = 
    match target with
      | None -> []
      | Some(n) -> [(target_to_mname n)]
  in
  let ast = parse_file file in
  let ((tdefs,instances,_),new_defs,_) =
    Process_file.check_ast_as_module all_targets mp init_env mod_name ast
  in
  let new_defs2 =
    match target with
      | None -> new_defs
      | Some(tgt) -> add_target_to_def tgt new_defs 
  in
    ((tdefs,instances), new_defs2)

let add_lib e1 e2 = env_union e1 e2

let add_open_lib k e1 e2 =
  match Nfmap.apply e2.m_env (Name.from_rope k) with
    | Some e ->
        env_union (env_union e1 e2) e.mod_env
    | None ->
        assert false

(* Process a library for the given target and open it in the current init_env *)
let proc_open target file (td,env) =
  let mod_name = filename_to_mod file in
  let (td, new_env) = process_lib target file mod_name (td,env) in
    (td, add_open_lib mod_name env new_env)

(* Process a library for the given target *)
let proc target file (td,env) =
  let mod_name = filename_to_mod file in
  let (td, new_env) = process_lib target file mod_name (td,env) in
    (td, add_lib env new_env)

(* TODO: Add to the constants *)
let add_to_init targ file ((td,env), consts) =
  let targ_env = 
    match Nfmap.apply env.m_env (target_to_mname targ) with 
      | Some(e) -> e
      | None -> 
          assert false
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
  let starg = Some(targ) in
  let (new_td,new_env) = p starg file (td,targ_env.mod_env) in
    ((new_td, 
      { env with m_env = Nfmap.insert env.m_env (target_to_mname targ, {targ_env with mod_env = new_env}) }), 
     consts)

module Initial_libs (P : sig val path : string end) =
struct
  open P

  let td = (initial_d, Pfmap.empty)

  let full_filename targ f = 
    List.fold_right Filename.concat [path; target_to_string targ] (f ^ ".lem")
  ;;

  (* HOL Env *)
  let (td, hol_env) = 
    List.fold_left
      (fun init_env t -> proc_open (Some(Target_hol)) (full_filename Target_hol t) init_env)
      (td,initial_env)
      ["min"; "bool"; "pair"; "arithmetic"; "pred_set"; "finite_map"; "list"; "string"; "sorting"; "set_relation"; "integer"]

  let target = Target_ocaml

  let holpath = Path.mk_path [] (target_to_mname Target_hol)
  let ocamlpath = Path.mk_path [] (target_to_mname Target_ocaml)
  let isapath = Path.mk_path [] (target_to_mname Target_isa)
  let coqpath = Path.mk_path [] (target_to_mname Target_coq)

  (* TODO: Remove so that the OCaml env can't refer to the HOL env *)
  let env =
    { initial_env with 
          m_env = 
            Nfmap.from_list [(target_to_mname Target_hol, { mod_binding = holpath; mod_env = hol_env })] }

  (* Coq Env *)
  let (td, coq_perv) =
    proc_open (Some Target_coq) (full_filename Target_coq "pervasives") (td, env)
  ;;

  let (td, coq_env) = 
    List.fold_left (
      fun init_env t ->
        proc (Some Target_coq) (full_filename Target_coq t) init_env
    ) (td, coq_perv)
    ["pervasives"; "set"; "list"] (* remove hol_env eventually when type synonyms work *)
  ;;
  
  (* OCAML Env *)
  let (td,ocaml_perv) = proc_open (Some(Target_ocaml)) (full_filename Target_ocaml "pervasives") (td,env)

  let (td, ocaml_env) = 
    List.fold_left
      (fun init_env t -> proc (Some(Target_ocaml)) (full_filename Target_ocaml t) init_env)
      (td,ocaml_perv)
      ["list"; "pset"; "pmap"; "nat_num" ; "vector" ; "bit"]
  
  
  (* Isabelle Env *)
  let (td,isa_perv) = proc_open (Some(Target_isa)) (full_filename Target_isa "pervasives") (td,env)

  let (td,isa_env) = 
      List.fold_left
        (fun init_env t -> proc_open (Some(Target_isa)) (full_filename Target_isa t) init_env)
        (td,isa_perv)
        ["pervasives";"list";"set";"finite_Set";"map"]   
        (* PS HACK - TEMPORARILY REMOVE IN HOPES OF GETTING HOL BUILD *)
  
  (*
  let (td,isa_env) =

    List.fold_left 
      (fun (td,isa_env) t -> proc (Some(Ast.Target_isa(None))) t td isa_env)
      (td,isa_perv)
      ["list"; "pred_set"]   *)  

  let env = {
    initial_env with
      m_env = Nfmap.from_list [
              (target_to_mname (Target_ocaml), { mod_binding = ocamlpath; mod_env = ocaml_env });
        (target_to_mname (Target_hol), { mod_binding = holpath; mod_env = hol_env });
        (target_to_mname (Target_isa), { mod_binding = isapath; mod_env = isa_env });
        (target_to_mname (Target_coq), { mod_binding = coqpath; mod_env = coq_env })
      ]
  }
  ;;

   
  let (td, perv) =
    proc_open None (Filename.concat path "pervasives.lem") (td, env)
  ;;

  let init =
    (List.fold_left (
       fun (td,env) t -> proc None (Filename.concat path (t ^ ".lem")) (td, env)
     ) (td, perv) ["list"; "set"; "pmap"; "int" ; "vector" ; "bit"],
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
