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

type t = P_prefix                (** a prefix operation *)
       | P_infix of int          (** a non-associative infix operation of the given precedence, higher precenced bind stronger *)
       | P_infix_left of int     (** a left-associative infix operation *)
       | P_infix_right of int    (** a right-associative infix operation *)
       | P_special               (** an operation with special syntax (e.g. if-then-else) *)

type context = 
  | Field
  | App_right
  | App_left
  | Infix_left of t
  | Infix_right of t
  | Delimited

type exp_kind =
  | App
  | Infix of t
  | Let
  | Atomic
        
type pat_context =
  | Plist
  | Pas_left
  | Pcons_left
  | Pcons_right
  | Pdelimited

type pat_kind =
  | Papp
  | Pas
  | Padd
  | Pcons
  | Patomic

val is_infix : t -> bool 

val needs_parens : context -> exp_kind -> bool
val pat_needs_parens : pat_context -> pat_kind -> bool

(** [get_prec target env c] looks up the precedence of constant [c] in environment [env]
    for the target [target]. Thereby, it follows target-representations of this constant.*)
val get_prec : Target.target -> Typed_ast.env -> Typed_ast.const_descr_ref -> t

(** [get_prec target env e] looks up the precedence of expression [e] in environment [env]
    for the target [target]. If the expression is essentially a constant (i.e. a constant
    with perhaps parenthesis or types added), the precedence of this constant is returned
    using [get_prec]. Otherwise [P_prefix] is returned. *)
val get_prec_exp : Target.target -> Typed_ast.env -> Typed_ast.exp -> t
