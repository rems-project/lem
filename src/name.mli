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

(** source-file and internal short identifiers *)

(** {2 plain names } *)

(** t is the type of plain names, names are essentially strings *)
type t

(** {3 basic functions on plain names } *)
val compare : t -> t -> int
val pp : Format.formatter -> t -> unit

val from_string : string -> t
val to_string : t -> string

val from_rope : Ulib.Text.t -> t
val to_rope : t -> Ulib.Text.t


(** {3 modifying names} *)

(** [rename r_fun n] renames [n] using the function [r_fun]. It looks at the 
  text representation [n_text] of [n] and returns then the name corresponding to
  [r_fun n_text]. *)
val rename : (Ulib.Text.t -> Ulib.Text.t) -> t -> t

(** [start_with_upper_letter n] checks, whether the name [n] starts with
    a character in the range [A-Z]. *)
val starts_with_upper_letter : t -> bool

(** [uncapitalize n] tries to uncapitalize the first letter of [n].
    If [n] does not start with a uppercase character, [None] is returned, otherwise 
    the modified name. *)
val uncapitalize : t -> t option

(** [start_with_lower_letter n] checks, whether the name [n] starts with
    a character in the range [a-z]. *)
val starts_with_lower_letter : t -> bool

(** [capitalize n] tries to capitalize the first letter of [n].
    If [n] does not start with a lowercase character, [None] is returned, otherwise 
    the modified name. *)
val capitalize : t -> t option

(** [start_with_underscore n] checks, whether the name [n] starts with
    an underscore character. *)
val starts_with_underscore : t -> bool

(** [remove_underscore n] tries to remove a leading underscores from name [n].
    If [n] does not start with an underscore character, [None] is returned, otherwise 
    the modified name. *)
val remove_underscore : t -> t option

(** [ends_with_underscore n] checks, whether the name [n] ends with
    an underscore character. *)
val ends_with_underscore : t -> bool

(** [remove_underscore_suffix n] tries to remove a suffix underscores from name [n].
    If [n] does not end with an underscore character, [None] is returned, otherwise 
    the modified name. *)
val remove_underscore_suffix : t -> t option

(** {3 generating fresh names} *)

(** [fresh n OK] generates a name [m], such that 
    [OK m] holds. [m] is of the form [n] followed by
    an integer postfix. First [n] without postfix is tried.
    Then counting up from 0 starts, till [OK] is satisfied. *)
val fresh : Ulib.Text.t -> (t -> bool) -> t

(** [fresh_num_list i n OK] generates a list of [i] fresh names. If no conflicts occur
    it returns a list of the form [[ni, n(i-1), ..., n1]]. Internally,
    [fresh n OK] is used [n] times. However, [OK] is updated to ensure, that
    the elemenst of the resulting list not only satisfy [OK], but are also distinct from each other. *)
val fresh_num_list : int -> Ulib.Text.t -> (t -> bool) -> t list

(** [fresh_list OK ns] builds variants of the names in list [ns] such that all elements of 
    the resulting list [ns'] satisfy [OK] and are distinct to each other.*)
val fresh_list : (t -> bool) -> t list -> t list



(** {2 names with whitespace an type} *)

(** [lskips_t] is the type of names with immediately preceding skips, i.e. whitespace or comments *)
type lskips_t

val lskip_pp : Format.formatter -> lskips_t -> unit

(** creates a name from Ast.x_l, used during typechecking *)
val from_x : Ast.x_l -> lskips_t

(** creates a name from Ast.ix_l, used during typechecking *)
val from_ix : Ast.ix_l -> lskips_t

(** [add_lskip] converts a name into a name with skips by adding empty whitespace *)
val add_lskip : t -> lskips_t

(** [strip_lskip] converts a name with whitespace into a name by dropping the preceeding whitespace *)
val strip_lskip : lskips_t -> t

(** [get_lskip n] gets the preceeding whitespace of [n] *)
val get_lskip : lskips_t -> Ast.lex_skips

(** [add_pre_lskip sk n] adds additional whitespace in front of [n] *)
val add_pre_lskip : Ast.lex_skips -> lskips_t -> lskips_t

(** [replace_lskip sk n] replaces the whitespace in front of [n] with [sk]. The old whitespace is
    thrown away. *)
val replace_lskip : lskips_t -> Ast.lex_skips -> lskips_t

(** [lskip_rename r_fun n] is a version of [rename] that can handle lskips. It renames [n] using 
    the function [r_fun] and preserves the original whitespace. *)
val lskip_rename : (Ulib.Text.t -> Ulib.Text.t) -> lskips_t -> lskips_t

(** {2 output functions} *)

(** [to_output_format format_fun id_annot n] formats the name [n] as output. A name with output consists of preedeing whitespace, 
    the name as a text and a name-type. The space is formated using [ws], the other componenst together with [id_annot] are formated 
    with [format_fun]. *)
val to_output_format : (Output.id_annot -> Ulib.Text.t -> Output.t) -> Output.id_annot -> lskips_t -> Output.t

(** [to_output] is the same as [to_output_format Output.id] *)
val to_output : Output.id_annot -> lskips_t -> Output.t

(** [to_output_quoted qs_begin qs_end id_annot n] formats [n] with the quoting strings [qs_begin] and [qs_end] added before and after respectively. *)
val to_output_quoted : string -> string -> Output.id_annot -> lskips_t -> Output.t

(** [to_rope_tex a n] formats [n] as [a] for the tex-backend as a string. The preceeding whitespace is ignored. *)
val to_rope_tex : Output.id_annot -> t -> Ulib.Text.t
