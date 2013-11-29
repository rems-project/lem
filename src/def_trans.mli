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

(** {2 Infrastructure form definition macros} *)

(** [def_macro] is the type of definition macros. A definition macro [def_mac] gets the arguments
    [rev_path], [env] and [d]. The argument [d] is the definition the macro should process.
    [rev_path] represents the path of the module of definition [d] as a list of names in reverse order.
    [env] is the local environment for the module of [d]. This means that also the definitions in
    the same module that follow [d] are present. If the macro does not modify the definition, it should
    return [None]. Otherwise, it should return a pair [Some (env', ds)], where [env'] is a updated environment 
    and [ds] a list of definitions that replace [d]. *)
type def_macro = Name.t list -> env -> def -> (env * def list) option

(** [list_to_mac macro_list] collapses a list of [def_macros] into a single one.
    It looks for the first macro in the list that succeeds, i.e. returns not [None] and
    returns the result of this macro. *)
val list_to_mac : def_macro list -> def_macro

(** [process_defs rev_path def_mac mod_name env ds] is intended to run the macro [def_mac] over all
    definitions in module [mod_name]. The argument [rev_path] is the path to module [mod_name] in reversed order.
    [env] is the environment containing module [mod_name] and [ds] is the list of definitions in this module.
    If [def_mac] modifies a definition [d] to a list [ds], it is then run on all definitions in [ds].     
    If one of the is a module-definition, which is not modified by [ds], then [def_macro] is run 
    on all definitions inside this module. For this recursive call the path, module name and environment are adapted.

    The result of [process_defs] is an updated environment and a new list of definitons. *)
val process_defs : Name.t list -> def_macro -> Name.t -> env -> def list -> (env * def list)


(** {2 Dictionary passing} *)

(** Type classes are not supported by all backends. The [def_macro] [class_to_record] takes a
    definition of a type class and turns it into a definition of a record type. The methods of the
    class become field of the record. This record can then be used as the dictionary type for the
    dictionary passing. *)
val class_to_record : Target.target -> def_macro

(** Removes inline instances for backends that employ typeclasses. *)
val comment_out_inline_instances_and_classes : Target.target -> def_macro

(** [instance_to_dict do_inline targ] turns instance declarations into a definition of a dictionary record.
    If [do_inline] is set, this definition will be inlined (for this the target argument is needed). *)
val instance_to_dict : bool -> Target.target -> def_macro

val class_constraint_to_parameter : Target.target -> def_macro


(** {2 Open / Include / Import} *)

(** [remove_opens] removes all open / include and import statements *)
val remove_opens : def_macro

(** [remove_import_include] removes all import and include statements. Imports are deleted and
    includes turned into open statements. *)
val remove_import_include : def_macro

(** [remove_import] removes all import statements. *)
val remove_import : def_macro

(** [remove_module_renames] removes all module rename statements. *)
val remove_module_renames : def_macro

(** {2 Misc} *)

(** If a target representation for a type is given, the original type definition is commented out.
    Notice that target-specific renamings are not target representations. *)
val remove_types_with_target_rep : Target.target -> def_macro

(** If a target representation for a constant is given, the original definition is not needed.
    However, turn this definition into a lemma to ensure that the target representation is sensible. *)
val defs_with_target_rep_to_lemma : env -> Target.target -> def_macro


val remove_vals : def_macro
val remove_indrelns : def_macro
val remove_indrelns_true_lhs : def_macro
val remove_classes : def_macro
val type_annotate_definitions : def_macro
val nvar_to_parameter : def_macro

val prune_target_bindings : Target.non_ident_target -> def list -> def list



