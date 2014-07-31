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

(** Datatype and Function for Targets *)

(** A datatype for Targets. In contrast to the one in
    [ast.ml] this one does not carry white-space information. *)
type non_ident_target = 
  | Target_hol
  | Target_ocaml
  | Target_isa
  | Target_coq
  | Target_tex
  | Target_html
  | Target_lem

(** [target] for the typechecked ast is either a real target as in the AST or
    the identity target *)
type target =
  | Target_no_ident of non_ident_target 
  | Target_ident

(** [ast_target_to_target t] converts an ast-target to a
    target. This essentially means dropping the white-space information. *)
val ast_target_to_target : Ast.target -> non_ident_target

(** [target_to_ast_target t] converts a target [t] to an
    ast_target. This essentially means adding empty white-space information. *)
val target_to_ast_target : non_ident_target -> Ast.target

(** [ast_target_compare] is a comparison function for ast-targets. *)
val ast_target_compare : Ast.target -> Ast.target -> int

(** [target_compare] is a comparison function for targets. *)
val target_compare : non_ident_target -> non_ident_target -> int

(** target keyed finite maps *)
module Targetmap : sig
   include Finite_map.Fmap with type k = non_ident_target

   (** [apply_target m targ] looks up the [targ] in map [m]. 
       Target-maps only store information for real targets, not the identity one.
       If therefore [targ] is [Target_ident], i.e. represents the identity backend,
       [None] is returned. *)
   val apply_target : 'a t -> target -> 'a option

   (** [insert_target m (targ, v)] inserts value [v] for [targ] in map [m]. 
       Target-maps only store information for real targets, not the identity one.
       If therefore [targ] is [Target_ident], i.e. represents the identity backend,
       the map is not(!) updated. *)
   val insert_target : 'a t -> (target * 'a) -> 'a t
end

(** target sets *)
module Targetset : Set.S with type elt = non_ident_target

(** A list of all the targets. *)
val all_targets_list : non_ident_target list

(** The set of all the targets. *)
val all_targets : Targetset.t

(** The set of targets used when negating or no mentioning explicit targets. Targets like Lem are excluded by default. *)
val all_targets_non_explicit : Targetset.t

(** The set of targets that can handle only executable definitions. 
    Currently only Ocaml, but this might change. *)
val all_targets_only_exec : Targetset.t
val all_targets_only_exec_list : non_ident_target list

(** [non_ident_target_to_string t] returns a string description of a target [t]. *)
val non_ident_target_to_string : non_ident_target -> string

(** [target_to_string t_opt] returns a string description of a target.
    If some target is given, it does the same as [target_to_string]. Otherwise,
    it returns a string description of the identity backend. *)
val target_to_string : target -> string

(** [non_ident_target_to_mname t] returns a name for a target. It is similar to
    [non_ident_target_to_string t]. However, it returns capitalised versions. *)
val non_ident_target_to_mname : non_ident_target -> Name.t

(** [target_to_output t] returns output for a target [t]. *)
val target_to_output : Ast.target -> Output.t

(** [is_human_target targ] checks whether [targ] is a target intended to be read by humans
    and therefore needs preserving the original structure very closely. Examples for such targets are
    the tex-, html- and identity-targets. *)
val is_human_target : target -> bool

(** [is_tex_target targ] checks whether [targ] is the TeX target. *)
val is_tex_target : target -> bool

(** [suppress_targets targ tex_flag] returns whether a target must print let-bindings
    defined for a subset of target backends as normal let-bindings in the TeX backend. *)
val suppress_targets : target -> bool -> bool

(** [dest_human_target targ] destructs [targ] to get the non-identity target. If it s a human-target, 
    [None] is returned, otherwise the non-identity target. *)
val dest_human_target : target -> non_ident_target option
