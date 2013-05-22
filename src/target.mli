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
type target = 
  | Target_hol
  | Target_ocaml
  | Target_isa
  | Target_coq
  | Target_tex
  | Target_html

(** [ast_target_to_target t] converts an ast-target to a
    target. This essentially means dropping the white-space information. *)
val ast_target_to_target : Ast.target -> target

(** [target_to_ast_target t] converts a target [t] to an
    ast_target. This essentially means adding empty white-space information. *)
val target_to_ast_target : target -> Ast.target

(** [ast_target_compare] is a comparison function for ast-targets. *)
val ast_target_compare : Ast.target -> Ast.target -> int

(** [target_compare] is a comparison function for targets. *)
val target_compare : target -> target -> int

(** target keyed finite maps with a default value*)
module Targetmap : Finite_map.Dmap with type k = target

(** target sets *)
module Targetset : Set.S with type elt = target

(** The set of all the targets. *)
val all_targets : Targetset.t

(** [target_to_string t] returns a string description of a target [t]. *)
val target_to_string : target -> string

(** [target_opt_to_string t_opt] returns a string description of a target.
    If some target is given, it does the same as [target_to_string]. Otherwise,
    it returns a string description of the identity backend. *)
val target_opt_to_string : target option -> string

(** [target_to_mname t] returns a name for a target. It is similar to
    [target_to_string t]. However, it returns capitalised versions. *)
val target_to_mname : target -> Name.t

(** [target_to_output a t] returns output for a target [t] and id-annotation [a]. *)
val target_to_output : Output.id_annot -> Ast.target -> Output.t
