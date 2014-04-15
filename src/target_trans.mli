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
open Target

(** [get_transformation targ] returns the (pre-backend) transformation function for target [targ] *)
val get_transformation : target -> (env -> checked_module -> (env * checked_module))

(** [get_avoid_f targ] returns the target specific variable avoid function. Before this function
    can be used, it needs to get the set of constants to avoid. *)
val get_avoid_f : target -> (NameSet.t -> var_avoid_f)

(** [add_used_entities_to_avoid_names env targ ue ns] adds the used entities in [ue] to the name-set
    [ns]. This nameset is intended to contain the names to avoid when using [get_avoid_f] or [rename_def_params].
    Since for each target different names need to be avoided, the intended target is required as well. Finally,
    the environment is needed to look-up target representations. *)
val add_used_entities_to_avoid_names : env -> target -> Typed_ast_syntax.used_entities -> NameSet.t -> NameSet.t
  
(** Rename the arguments to definitions, if they clash with constants in a given set of constants.
   This was previously part of the transformation returned by get_transformation. It got moved
   out in order to see all the renamings of definitions before changing their arguments. *)
val rename_def_params : target -> NameSet.t -> checked_module list -> checked_module list

(** This flag enables pattern compilation for the identity backend. Used for debugging. *)
val ident_force_pattern_compile : bool ref

(** This flag enables dictionary passing transfromations for the identity backend. Used for debugging. *)
val ident_force_dictionary_passing : bool ref 

(** This flag enables removing top-level matches from definition for the HOL4 backend. *)
val hol_remove_matches : bool ref

(** This flag enables the removing of failwith and fail (from library module Assert_extra) in the
    prover backends in favour of a partial pattern match that will then be handled by pattern match
    compilation.  At Peter and Shaked's request.
*)
val prover_remove_failwith : bool ref

