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

module StringSet = Set.Make(
struct 
  type t = string
  let compare = Pervasives.compare
end)

module StringSetExtra = Util.ExtraSet(StringSet)

open Types

type module_dependency = {
   module_name : string;
   module_filename : string;
   module_ast : Ast.defs * Ast.lex_skips;
   missing_deps : StringSet.t;
   module_needs_output : bool
}
  
let module_dependency_is_resolved md =
  StringSet.is_empty md.missing_deps 

let module_dependency_is_cyclic md =
  StringSet.mem md.module_name md.missing_deps 

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
let search_module_file mod_name =
  let filename = modname_to_filename mod_name in

  (* TODO: be more clever here *)
  let dir_prefix = "" in

  dir_prefix ^ filename



let load_module_file (filename, needs_output) =
  let ast = Process_file.parse_file filename in

  let missing_deps = begin
    let needed_modules = Ast_util.get_imported_modules ast in
    let needed_modules_top = List.map Path.get_toplevel_name needed_modules (* only top_level modules can be loaded by files *) in
    let needed_module_strings = List.map (fun n -> String.capitalize (Name.to_string n)) needed_modules_top in
    StringSetExtra.from_list needed_module_strings
  end in

  { 
    module_name = filename_to_modname filename;
    module_filename = filename;
    module_ast = ast;
    missing_deps = missing_deps;
    module_needs_output = needs_output;
  }


(** [load_module tries to load the module with name [module_name] *)
let load_module module_name =
  let module_file_name = search_module_file module_name in
  load_module_file (module_file_name, false)


(** [resolve_dependencies ordered_modules missing_modules] tries to solve dependencies by
    ordering the modules in [missing_modules]. The list [ordered_modules] have already
    been loaded. *)      
let rec resolve_dependencies 
  (resolved_modules : module_dependency list)
  (missing_modules : module_dependency list) : module_dependency list =
match missing_modules with
  | [] -> (* we are done *) List.rev resolved_modules
  | md :: missing_modules' ->
    begin
      (* remove already processed modules from the dependencies *)
      let md = begin
         let resolved_modules_list = List.map (fun md' -> md'.module_name) resolved_modules in
         {md with missing_deps = StringSetExtra.remove_list md.missing_deps resolved_modules_list}
      end in

      if module_dependency_is_resolved md then          
        (* md is OK, we can typecheck it now *)
        resolve_dependencies (md :: resolved_modules) missing_modules'
      else if module_dependency_is_cyclic md then
        (* a dependency cycle was detected *)
        Reporting_basic.report_error (Reporting_basic.Err_cyclic_build md.module_name)
      else begin
        (* choose an aribitray missing depency and process it *)
        let missing_dep = StringSet.choose md.missing_deps in
        match Util.list_pick (fun md' -> md'.module_name = missing_dep) missing_modules' with
          | Some (md', missing_modules'') ->
              (* md depends on already parsed module md'. Therefore, process md' first and 
                 for cycle-detection make sure the depencies of md' are also dependencies of md. *)
              let md = {md with missing_deps = StringSet.union md.missing_deps md'.missing_deps} in
              resolve_dependencies resolved_modules (md' :: md :: missing_modules'')
          | None ->
              (* md depends on a module that has not been parsed yet. Try to find a file containing it
                 and load this file *)
              let md' = load_module missing_dep in
              resolve_dependencies resolved_modules (md' :: md :: missing_modules')
      end
    end  


let process_files (files : (string * bool) list) =
begin
  let missing_modules = List.map load_module_file files in
  let resolved = resolve_dependencies [] missing_modules in

  List.map (fun md -> (md.module_name, md.module_filename, md.module_ast, md.module_needs_output)) resolved
end
