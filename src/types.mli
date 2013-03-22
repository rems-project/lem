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

type tnvar =
  | Ty of Tyvar.t
  | Nv of Nvar.t

val pp_tnvar: Format.formatter -> tnvar -> unit
val tnvar_to_rope: tnvar -> Ulib.Text.t
val tnvar_compare: tnvar -> tnvar -> int

module TNvar : sig
  type t = tnvar
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module Pfmap : Finite_map.Fmap with type k = Path.t
module TNfmap : Finite_map.Fmap with type k = TNvar.t
module TNset : sig
  include Set.S with type elt = TNvar.t
  val pp : Format.formatter -> t -> unit
end

type t_uvar
type n_uvar
type t = { mutable t : t_aux }
and t_aux =
  | Tvar of Tyvar.t
  | Tfn of t * t
  | Ttup of t list
  | Tapp of t list * Path.t
  | Tne of nexp
  | Tuvar of t_uvar
and nexp = { mutable nexp : nexp_aux }
and nexp_aux =
  | Nvar of Nvar.t
  | Nconst of int
  | Nadd of nexp * nexp
  | Nmult of nexp * nexp
  | Nneg of nexp (* Unary minus for representing new vector sizes after vector slicing *)
  | Nuvar of n_uvar

(* Constraints for nexps, plus the location which added the constraint, each nexp is either <= 0 = 0 or >= 0 *)
type range =
  | LtEq of Ast.l * nexp
  | Eq of Ast.l * nexp
  | GtEq of Ast.l * nexp

(* Structural comparison of types, without expanding type abbreviations.
 * Probably better not to use *)
val compare : t -> t -> int

val multi_fun : t list -> t -> t
val type_subst : t TNfmap.t -> t -> t
val free_vars : t -> TNset.t

val tnvar_to_name : tnvar -> Name.t
val tnvar_to_type : tnvar -> t
val tnvar_split : tnvar list -> (tnvar list * tnvar list)

type tc_def = 
  | Tc_type of tnvar list * t option * string option
  (* The class' type parameter, and the names and types of the methods *)
  | Tc_class of tnvar * (Name.t * t) list

type type_defs = tc_def Pfmap.t

(* The last Name.t list is to the module enclosing the instance declaration *)
type instance = tnvar list * (Path.t * tnvar) list * t * Name.t list

val head_norm : type_defs -> t -> t

val assert_equal : Ast.l -> string -> type_defs -> t -> t -> unit

(* Gets the instance for the given class and type.  Returns None if there is
 * none.  The returned Name list is to the module enclosing the instance
 * declaration.  The returned map is the instantiation of the instances type
 * variables.  The returned list is the set of instances that the found instance
 * relies on. *)
val get_matching_instance : type_defs -> (Path.t * t) -> instance list Pfmap.t -> 
          (Name.t list * t TNfmap.t * (Path.t * t) list) option

(* Convert a list of nexp into a binary sumation *)
val nexp_from_list : nexp list -> nexp

module type Global_defs = sig
  val d : type_defs 
  val i : (instance list) Pfmap.t 
end 

module Constraint (T : Global_defs) : sig
  val new_type : unit -> t
  val new_nexp : unit -> nexp
  val equate_types : Ast.l -> t -> t -> unit
  val in_range : Ast.l -> nexp -> nexp -> unit
  val add_constraint : Path.t -> t -> unit
  val add_tyvar : Tyvar.t -> unit 
  val add_nvar : Nvar.t -> unit
  val inst_leftover_uvars : Ast.l -> TNset.t * (Path.t * tnvar) list
end

val pp_type : Format.formatter -> t -> unit
val pp_nexp : Format.formatter -> nexp -> unit
val pp_class_constraint : Format.formatter -> Path.t * tnvar -> unit
val pp_instance : Format.formatter -> instance -> unit

val t_to_string : t -> string

(* converts the type into the default name of auto-generated variables of this type *)
val t_to_var_name : t -> Name.t
