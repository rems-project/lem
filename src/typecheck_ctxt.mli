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
(*          Brian Campbell, University of Edinburgh                       *)
(*          Shaked Flur, University of Cambridge                          *)
(*          Thomas Bauereiss, University of Cambridge                     *)
(*          Stephen Kell, University of Cambridge                         *)
(*          Thomas Williams                                               *)
(*          Lars Hupel                                                    *)
(*          Basile Clement                                                *)
(*                                                                        *)
(*  The Lem sources are copyright 2010-2018                               *)
(*  by the authors above and Institut National de Recherche en            *)
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

(* As we process definitions, we need to keep track of the type definitions
 * (type_defs), class instance definitions (instance list Pfmap.t) and
 * function/value/module/field (env) definitions we encounter. *)
type defn_ctxt = { 
  (* All type definitions ever seen *) 
  all_tdefs : Types.type_defs; 

  (* The global c_env *)
  ctxt_c_env : Typed_ast.c_env;

  (* The global e_env (module environment) *)
  ctxt_e_env : Typed_ast.mod_descr Types.Pfmap.t;

  (* All class instances ever seen *)
  all_instances : Types.i_env;

  (* The names of all assertions / lemmata defined. Used only to avoid using names multiple times. *)
  lemmata_labels : Typed_ast.NameSet.t; 

  (* The target-reps of current top-level module. *)
  ctxt_mod_target_rep: Typed_ast.mod_target_rep Target.Targetmap.t;

  (* does the module apear in output ? *)
  ctxt_mod_in_output : bool;

  (* The current value/function/module/field/type_name environment *)
  cur_env : Typed_ast.local_env;

  (* The value/function/module/field/type_names defined in this sequence of
   * definitions *)
  new_defs : Typed_ast.local_env;

  (* The value/function/module/field/type_name environment to export *)
  export_env : Typed_ast.local_env;

  (* All types defined in this sequence of definitions *)
  new_tdefs : Path.t list;

  (* All class instances defined in this sequence of definitions *)
  new_instances : Types.instance_ref list;
}

(** The distinction between [cur_env], [new_defs] and [export_env] is interesting.
    [cur_env] contains the local environment as seen by a function inside the module.
    [new_defs] in contrast contains only the definitions made inside the module. It is
    used to check for duplicate definitions. [export_env] is the outside view of the module.
    It contains all definitions made inside the module (i.e. [new_defs]) as well as
    the included modules (see command [include]). *)
val add_d_to_ctxt : defn_ctxt -> Path.t -> Types.tc_def -> defn_ctxt
val add_p_to_ctxt : defn_ctxt -> Name.t * (Path.t * Ast.l) -> defn_ctxt
val add_f_to_ctxt : defn_ctxt -> Name.t * Types.const_descr_ref -> defn_ctxt
val add_v_to_ctxt : defn_ctxt -> Name.t * Types.const_descr_ref -> defn_ctxt
val union_v_ctxt  : defn_ctxt -> Typed_ast.const_descr_ref Typed_ast.Nfmap.t -> defn_ctxt


val add_m_to_ctxt : Ast.l -> defn_ctxt -> Name.t -> Typed_ast.mod_descr -> defn_ctxt
val add_m_alias_to_ctxt : Ast.l -> defn_ctxt -> Name.t -> Path.t -> defn_ctxt
val add_instance_to_ctxt : defn_ctxt -> Types.instance -> defn_ctxt * Types.instance_ref
val add_lemma_to_ctxt : defn_ctxt -> Name.t -> defn_ctxt

(** A definition context contains amoung other things an environment split up over several fields.
    This functions extracts this environment. *)
val defn_ctxt_to_env : defn_ctxt -> Typed_ast.env

(** [ctxt_c_env_set_target_rep l ctxt c targ new_rep] updates the target-representation of
    constant [c] for target [targ] in context [ctxt] to [new_rep]. This results into a new
    environment. If an representation was already stored (and is now overridden), it is returned as well. 
    If it can't be overriden, an exception is raised. *)
val ctxt_c_env_set_target_rep : Ast.l -> defn_ctxt -> Typed_ast.const_descr_ref -> Target.non_ident_target ->
           Typed_ast.const_target_rep -> defn_ctxt * Typed_ast.const_target_rep option

(** [ctxt_all_tdefs_set_target_rep l ctxt ty targ new_rep] updates the target-representation of
    type [ty] for target [targ] in context [ctxt] to [new_rep]. This results into a new
    environment. If an representation was already stored (and is now overridden), it is returned as well. *)
val ctxt_all_tdefs_set_target_rep : Ast.l -> defn_ctxt -> Path.t -> Target.non_ident_target ->
           Types.type_target_rep -> defn_ctxt * Types.type_target_rep option

(** [ctxt_all_tdefs_set_target_sorts l ctxt ty targ new_sorts] updates the target sort annotations of
    type [ty] for target [targ] in context [ctxt] to [new_sorts]. This results into a new
    environment. If an representation was already stored (and is now overridden), it is returned as well. *)
val ctxt_all_tdefs_set_target_sorts : Ast.l -> defn_ctxt -> Path.t -> Target.non_ident_target ->
           Types.sort list -> defn_ctxt * (Ast.l * Types.sort list) option


(** [ctxt_start_submodule ctxt] is used when a new submodule is processed. It resets all the
    new-information like the field [new_defs], but keeps the other informations (including
    the current environment) around. *)
val ctxt_begin_submodule : defn_ctxt -> defn_ctxt

(** [ctxt_end_submodule l ctxt_before mod_path mod_name ctxt_submodule] is used when a new submodule is no longer processed. 
    It resets some information (like the local environment of [ctxt_submodule] back to the values
    in [ctxt_before]. The context [ctxt_before] is supposed to be the one valid before
    starting to process the submodule. The new definitions of the submodule are moved to
    a new module [mod_name] at path [mod_path].*)
val ctxt_end_submodule : Ast.l -> defn_ctxt -> Name.t list -> Name.t -> defn_ctxt -> defn_ctxt

