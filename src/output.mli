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

(** Intermediate output format before going to strings *)

(* The main type of output *)
type t

(* A simplified version of the output type *)
type t' =
  | Kwd' of string
  | Ident' of Ulib.Text.t
  | Num' of int

(** kind annotation for latex'd identifiers *)
type id_annot =  
  | Term_const of bool * bool (** [Term_const(is_quotation, needs_escaping)] *)
  | Term_field
  | Term_method 
  | Term_var 
  | Term_var_toplevel
  | Term_spec 
  | Type_ctor of bool * bool  (** [Term_ctor(is_quotation, needs_escaping)] *)
  | Type_var
  | Nexpr_var
  | Module_name
  | Class_name
  | Target
  | Component

(** {2 constructing output} *)

(** Empty output *)
val emp : t

(** [kwd s] constructs the output for keyword [s] *)
val kwd : string -> t

(** [num i] constructs the output for number [i] *)
val num : int -> t

(** [str s] constructs the output for string constant [s] *)
val str : Ulib.Text.t -> t

(** Whitespace *)
val ws : Ast.lex_skips -> t

(** [err message] is an error output. An exception is thrown with the given [message]
    if this output is created. Used for marking problems. *)
val err : string -> t

(** [meta s] creates a string directly as output such that the formatting can't interfere
    with string [s] any more *)
val meta : string -> t

(** A comment *)
val comment : string -> t

(** [comment_block min_width_opt content] comment a whole 
    list of lines in a block. *)
val comment_block : int option -> string list -> t

(** a new line *)
val new_line : t

(** a single space *)
val space : t

(** ??? Unsure what it is. Some kind of tex specific space, similar to space, but
    treated slightly differently by the Latex backend. It seems to be for example removed
    at beginnings and ends of lines and multiple ones are collapsed into a single space. *)
val texspace :  t


(** An identifier *)
val id : id_annot -> Ulib.Text.t -> t

(** [o1 ^ o2] appends to outputs to each other *)
val (^) : t -> t -> t

(** [flat [o0; ...; on]] appends all the outputs in the list, i.e.
    it does [o0 ^ ... ^ on]. *)
val flat : t list -> t

(** [concat sep [o0; ...; on]] appends all the outputs in the list using
    the separator [sep], i.e.
    it does [o0 ^ sep ^ o1 ^ ... sep ^ tn].*)
val concat : t -> t list -> t

(** [prefix_if_not_emp o1 o2] returns [o1 ^ o2] if [o2] is not empty and
    [emp] otherwise *)
val prefix_if_not_emp : t -> t -> t

(** {2 Pretty Printing} *)

(** {3 Blocks} 
    Blocks are used for pretty printing if the original whitespace should not be used. 
    This is usually the case, if the source was generated by some macro, such that 
    either no original spacing is present or it is likely to be broken. 
    If the first argument of a block is [true] this block and all it's content is
    printed using OCaml's [Format] library. The other arguments of blocks correspond
    to blocks in the [Format] library. They describe indentation, the type of block and the
    content. *)

val block : bool -> int -> t -> t
val block_h : bool -> int -> t -> t
val block_v : bool -> int -> t -> t
val block_hv : bool -> int -> t -> t
val block_hov : bool -> int -> t -> t


(** [core out] is a marker for marking the most important part of some output. It marks for example the
    rhs of a definition. Together with [extract_core] this is used to sometimes only print the most essential part
    of some output *)
val core : t -> t

(** [remove_core o] removes all occurences of core form [t] by replacing [core o'] with just [o']. *)
val remove_core : t -> t

(** [extract_core o] extracts all top-level cores from output [o]. *)
val extract_core : t -> t list

(** {3 Spacing} *) 

(** [removes intial whitespace (including comments) from output] *)
val remove_initial_ws : t -> t

(** [break_hint add_space ind] is a general hint for a line-break. If [add_space] is set
    a space is added in case no line-break is needed. Otherwise a line-break with the given 
    indentation [ind] is applied. *)
val break_hint : bool -> int -> t

(** [break_hint_cut] is short for [break_hint false 0]. It allows a newline at this posistion
    without indentation. If no newline is needed don't add any space. *)
val break_hint_cut : t

(** [break_hint_space ind] is short for [break_hint true ind]. 
    It adds a space or a newline. If a newline is needed use the given indentation. *)
val break_hint_space : int -> t

(** Make sure there is a newline starting here. This inserts a newline if necessary. *)
val ensure_newline : t


(** {2 Output to Rope} *)

(** [to_rope quote_char lex_skips_to_rope need_space t] formats the output [t] as an unicode text.
The [quote_char] argument is used around strings. The function [lex_skips_to_rope] is used to format
whitespace. Finally the function [need_space] is used to determine, whether an extra space is needed between
simplified outputs. *)
val to_rope : Ulib.Text.t -> (Ast.lex_skip -> Ulib.Text.t) -> (t' -> t' -> bool) -> t -> Ulib.Text.t

(** [ml_comment_to_rope com] formats an ML-comment as a text by putting [(*] and [*)] around it. *)
val ml_comment_to_rope : Ast.ml_comment -> Ulib.Text.t


(** {2 Latex Output} *)

(** [to_rope_tex t] corresponds to [to_rope] for the Latex backend. Since it is used for only one backend,
    the backend parameters of [to_rope] can be hard-coded.  *)
val to_rope_tex : t -> Ulib.Text.t 

(** [to_rope_option_tex t] is similar to [to_rope_tex t]. However, it checks whether the
    result is an empty text and returns [None] is in this case. *)
val to_rope_option_tex : t -> Ulib.Text.t option

val tex_escape : Ulib.Text.t -> Ulib.Text.t
val tex_escape_string : string -> string
val tex_command_escape : Ulib.Text.t -> Ulib.Text.t
val tex_command_label  : Ulib.Text.t -> Ulib.Text.t
val tex_command_name  : Ulib.Text.t -> Ulib.Text.t

