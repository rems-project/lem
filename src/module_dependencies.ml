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

module DepSet = Set.Make(
struct 
  type t = (string * Ast.l)
  let compare = Pervasives.compare
end)

module DepSetExtra = Util.ExtraSet(DepSet)

open Types

type module_dependency = {
   module_name : string;
   module_loc : Ast.l;
   module_filename : string;
   module_ast : Ast.defs * Ast.lex_skips;
   missing_deps : DepSet.t;
   module_needs_output : bool;
   module_given_by_user : bool
}
  
let module_dependency_is_resolved md =
  DepSet.is_empty md.missing_deps 

let module_dependency_is_cyclic md =
  DepSet.exists (fun (n, _) -> n = md.module_name) md.missing_deps 

(** convert a filename to a module name by capitalising it and chopping the
    extension ".lem" *)
let filename_to_modname filename = 
  let filename_base = Filename.basename (Filename.chop_extension filename) in
  String.capitalize filename_base

(** convert a module name to a file name by uncapitalising it and adding the
    extension ".lem" *)
let modname_to_filename modname = 
  String.uncapitalize (modname ^ ".lem")

(** [search_module_file mod_name] searches for the file a module [mod_name].
    This can be done arbitrarily clever, e.g. by searching a list of given
    directories.
*)
let search_module_file l search_dirs mod_name =
  let filename = modname_to_filename mod_name in

  let check_dir dir = begin
    let filename' = Filename.concat dir filename in
    if Sys.file_exists filename' then
      Some filename'
    else None 
  end in

  match Util.option_first check_dir search_dirs with
    | Some f -> (* filename found :-) *) f
    | None -> raise (
       Reporting_basic.Fatal_error (Reporting_basic.Err_resolve_dependency (l, search_dirs, mod_name)))
        



let load_module_file (filename, loc, needs_output, is_user_import) =
  let _ = if (not is_user_import) then Reporting.report_warning_no_env (Reporting.Warn_import (loc, filename_to_modname filename, filename)) else () in
  let ast = Process_file.parse_file filename in

  let missing_deps = begin
    let needed_modules = Ast_util.get_imported_modules ast in
    let needed_modules_top = List.map (fun (n, l) -> ((Path.get_toplevel_name n), l)) needed_modules (* only top_level modules can be loaded by files *) in
    let needed_module_strings = List.map (fun (n, l) -> (String.capitalize (Name.to_string n), l)) needed_modules_top in
    DepSetExtra.from_list needed_module_strings
  end in
  { 
    module_name = filename_to_modname filename;
    module_loc = loc;
    module_filename = filename;
    module_ast = ast;
    missing_deps = missing_deps;
    module_needs_output = needs_output;
    module_given_by_user = is_user_import;
  }


(** [load_module] tries to load the module with name [module_name] *)
let load_module (l: Ast.l) (search_dirs : string list) (module_name : string) =
  let module_file_name = search_module_file l search_dirs module_name in
  load_module_file (module_file_name, l, false, false)


(** [resolve_dependencies ordered_modules missing_modules] tries to solve dependencies by
    ordering the modules in [missing_modules]. The list [ordered_modules] have already
    been loaded. *)      
let rec resolve_dependencies allow_input_reorder (lib_dirs : string list)
  (resolved_modules : module_dependency list)
  (missing_modules : module_dependency list) : module_dependency list =
match missing_modules with
  | [] -> (* we are done *) List.rev resolved_modules
  | md :: missing_modules' ->
    begin
      (* remove already processed modules from the dependencies *)
      let md = begin
         let resolved_modules_list = List.map (fun md' -> md'.module_name) resolved_modules in
         {md with missing_deps = DepSet.filter (fun (n, _) -> not (List.mem n resolved_modules_list)) md.missing_deps }
      end in

      if module_dependency_is_resolved md then          
        (* md is OK, we can typecheck it now *)
        resolve_dependencies allow_input_reorder lib_dirs (md :: resolved_modules) missing_modules'
      else if module_dependency_is_cyclic md then
        (* a dependency cycle was detected *)
        raise (Reporting_basic.Fatal_error (Reporting_basic.Err_cyclic_build md.module_name))
      else begin
        (* choose an aribitray missing depency and process it *)
        let (missing_dep, dep_l) = DepSet.choose md.missing_deps in
        match Util.list_pick (fun md' -> md'.module_name = missing_dep) missing_modules' with
          | Some (md', missing_modules'') ->              
              (* md depends on already parsed module md'. Therefore, process md' first and 
                 for cycle-detection make sure the depencies of md' are also dependencies of md. *)

              let _ = if not ((not allow_input_reorder) && md'.module_given_by_user) then () else begin
                raise (Reporting_basic.Fatal_error (Reporting_basic.Err_reorder_dependency (dep_l, md'.module_name)))
              end in
                 
              let md = {md with missing_deps = DepSet.union md.missing_deps md'.missing_deps} in
              resolve_dependencies allow_input_reorder lib_dirs resolved_modules (md' :: md :: missing_modules'')
          | None ->
              (* md depends on a module that has not been parsed yet. Try to find a file containing it
                 and load this file *)
              let search_dirs = (Filename.dirname md.module_filename) :: lib_dirs in
              let md' = load_module dep_l search_dirs missing_dep in
              resolve_dependencies allow_input_reorder lib_dirs resolved_modules (md' :: md :: missing_modules')
      end
    end  


let process_files allow_input_reorder (lib_dirs : string list) (files : (string * bool) list) =
begin
  let files' = List.map (fun (n, i) ->  (n, Ast.Unknown, i, true)) files in
  let missing_modules = List.map load_module_file files' in
  let resolved = resolve_dependencies allow_input_reorder lib_dirs [] missing_modules in

  List.map (fun md -> (md.module_name, md.module_filename, md.module_ast, md.module_needs_output)) resolved
end
