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

(** macros for target_trans *)

open Typed_ast

exception Trans_error of Ast.l * string

type 'a macro = 'a -> 'a option
type pat_macro = Macro_expander.pat_position -> pat macro

module Macros (I : Types.Global_defs) (E : sig val env : env end) : sig 

  (** {2 Record Macros} *)
  (** [remove_single_to_record_updates] replaces updates of
      records that have only one field with the construction
      of a completely new record. *)
  val remove_singleton_record_updates : exp macro

  (** [sort_record_fields] sorts the fields of a record expression
      into the same order as in the definition of the record
      type. If they do not need resorting, everything is fine,
      otherwise a warning is produced. *)
  val sort_record_fields : exp macro

  (** {2 Set and List Comprehension Macros} *)

  (** [remove_list_comprehension] removes list comprehensions by turning
      them into fold and insert operations. A [Trans_error] exception is
      thrown, if not only bounded quantification is used. *)
  val remove_list_comprehension : exp macro

  (** [remove_set_comprehension] removes set comprehensions by turning
      them into fold and insert operations. A [Trans_error] exception is
      thrown, if not only bounded quantification is used. *)
  val remove_set_comprehension : exp macro

  (** [remove_set_comprehension allow_sigma] removes set comprehensions by turning
      them into set-image, set-filter and set-product operations. For example
      [{ f (x,y,z) | forall ((x,y) IN A) (z IN B) | P (x, y, z)}] is turned into
      [Set.image f (Set.filter P (Set.cross A B))]. If [allow_sigma] is set and the
      quantifiers depend on each other, [set_sigma] is used instead. So, for example
      [{ f (x,y,z) | forall ((x,y) IN A) (z IN B x) | P (x, y, z)}] is turned into
      [Set.image f (Set.filter P (Set.set_sigma A (fun (x, y) -> B x)))].

      In contrast to [remove_set_comprehension] no exception is thrown, if the translation fails. 
      This is because it is intended to be used
      with theorem prover backends, which can handle unbounded quantification differently.*)
  val remove_set_comprehension_image_filter : bool -> exp macro

  (** [remove_setcomp] removes set comprehensions with implicit bound variable to ones with
      explicitly bound onces. For example [{ (x, y) | x > y }] might, depending on context be turned
      in [{ (x, y) | forall x | x > y}], [{ (x, y) | forall x y | x > y}] or something similar.*)
  val remove_setcomp : exp macro

  (** [cleanup_set_quant] moves restricted and unrestricted quantification 
      in set comprehensions to the condition part, if the bound variables are only used by the condition.
      This means, that expressions of the form [{ f x | forall (p IN e) ... | P x }] become
      [{ f x | forall ... | exists (p IN e). P x }] if [x] is not a member of [FV p].
  *)
  val cleanup_set_quant : exp macro

  (** [remove_set_comp_binding] tries to turn [Comb_binding] expressions into [Set_comb] ones. 
      Given a term of the form [{ f x z | forall x z | P x z y1 ... yn }] it checks that only
      unbounded quantification is used and that the set of bound variables is exactly the set of free
      variables of the expression [f x z]. If this is the case, the expression is transformed to 
      [{ f x z | P x z y1 ... yn }]. Otherwise [remove_set_comp_binding] fails. *)
  val remove_set_comp_binding : exp macro

  (** [remove_set_restr_quant] turns restricted quantification in set comprehensions 
      into unrestricted quantification. Expressions of the form [{ f x | forall (p IN e) | P x }] become
      [{ f x | FV(p) | forall FV(p). p IN e /\ P x }]. This requires turning pattern [p] into
      an expression. This is likely to fail for more complex patterns. In these cases, [remove_set_restr_quant]
      fails and pattern compilation is needed. *)
  val remove_set_restr_quant : exp macro

  (** {2 Quantifier Macros} *)

  (** [list_quant_to_set_quant] turns [forall (x MEM L). P x] into [forall (x IN Set.from_list L). P x] *)
  val list_quant_to_set_quant : exp macro

  (** [remove_restr_quant pat_OK] turns restricted quantification into unrestricted quantification,
      if then pattern does not satisfy [pat_OK]. For example, expressions of the from [forall (p IN e). P x] becomes
      [forall FV(p). p IN e --> P x], if [pat_OK p] does not hold. [pat_OK] is used to configure, which types
      of restricted quantification are supported by the backend. For example, HOL 4 supports 
      patterns consisting of variables, tuples and wildcard patterns, while Isabelle does not like wildcard ones.
      This macros tries to turn pattern [p] into
      an expression. This is likely to fail for more complex patterns. In these cases, [remove_restr_quant pat_OK]
      fails and pattern compilation is needed. *)
  val remove_restr_quant : (pat -> bool) -> exp macro

  (** [remove_quant] turns quantifiers into iteration. It throws an [Trans_error] exception, if used
      on unrestricted quantification. Given an expression [forall (x IN X). P x] this returns
      [Set.forall X (fun x -> P x)]. It also works for existential quantification and quantification
      over lists. *)
  val remove_quant : exp macro

  (** {2 Pattern Macros} *)

  (** [remove_unit_pats] replaces unit-patterns [()] with wildcard ones [_]. *)
  val remove_unit_pats : pat_macro

  (** Warning: HOL specific! Transforms num-patterns of the form [n] or [x + n] into
      [SUC (SUC ...)]. *)
  val peanoize_num_pats_hol : pat_macro

  (** Warning: Isabelle specific! Transforms num-patterns of the form [n] or [x + n] into
      [Suc (Suc ...)]. *)
  val peanoize_num_pats_isa : pat_macro

  (** Add type annotations to pattern variables whose type contains a type variable
     (only add for arguments to top-level functions) *)
  val coq_type_annot_pat_vars : pat_macro

  (** {2 Misc} *)

  (** [do_substitutions target] does the inlining of target specific constant definitions *)
  val do_substitutions : target -> exp macro

  (** [remove_function] turns [function | pat1 -> exp1 ... | patn -> expn end] into
      [fun x -> match x with | pat1 -> exp1 ... | patn -> expn end]. *)
  val remove_function : exp macro

  (** Warning: OCaml specific! [remove_sets] transforms set expressions like [{e1, ..., en}] into
      [Ocaml.Pset.from_list (type_specific compare) [e1, ..., en]] *)
  val remove_sets : exp macro

  (** [remove_fun_pats keep_tup] removes patterns from expressions of the from
      [fun p1 ... pn -> e] by introducing [function] expressions. 
      Variable patterns and - if [keep_tup] is set - tuple patterns are kept. *)
  val remove_fun_pats : bool -> exp macro

  (** {2 Macros I don't understand} *)

  val hack : exp macro
  val tup_ctor : (exp -> exp) -> exp lskips_seplist -> exp macro
  val remove_class_const : exp macro
  val remove_method : exp macro
  val add_nexp_param_in_const : exp macro
  val remove_vector_access : exp macro
  val remove_vector_sub : exp macro

end
