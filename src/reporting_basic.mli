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

(** Basic error reporting

  [Reporting_basic] contains functions to report errors and warnings. 
  It contains functions to print locations ([Ast.l]) and lexing positions.
  Despite [Ast] it should not depend on any other Lem-file. This guarentees that
  it can be used throughout the whole devolpment.

  The main functionality is reporting errors. This is done by raising a
  [Fatal_error] exception. This is catched inside Lem and reported via [report_error]. 
  There are several predefined types of errors which all cause different error
  messages. If none of these fit, [Err_general] can be used.       

  Reporting functions that need access to parts of the Lem development like
  [Typed_ast] are collected in [Reporting]. 
*)

(** {2 Auxiliary Functions } *)

(** [loc_to_string short l] formats [l] as a string. If [short] is set, only the
    most originating location is formated, not what methods transformed [l]. *)
val loc_to_string : bool -> Ast.l -> string

(** [print_err fatal print_loc_source print_only_first_loc l head mes] prints an error / warning message to
    std-err. It starts with printing location information stored in [l]. If
    [print_loc_source] is set, the original input described by [l] is retrieved and shown.
    It then prints "head: mes". If [fatal] is set, the program exists with error-code 1 afterwards.
*)
val print_err : bool -> bool -> bool -> Ast.l -> string -> string -> unit

(** {2 Debuging } *)

(** Should debug be printed *)
val debug_flag : bool ref

(** [print_debug s] prints the string [s] with some debug prefix to the standard error output. *)
val print_debug : string -> unit 

(** {2 Errors } *)

(** In contrast to warnings, errors always kill the current run of Lem. They can't be recovered from. 
    [Err_todo] should not be used directly, but only through [err_todo] in order to make search easier.

    Errors usually have location information and a message attached. Some also carry a boolean flag indicating,
    the original source corresponding to the location information should be looked up and printed.
*)
type error = 
  | Err_general of bool * Ast.l * string
  (** General errors, used for multi purpose. If you are unsure, use this one. *)

  | Err_unreachable of Ast.l * string
  (** Unreachable errors should never be thrown. It means that some
      code was excuted that the programmer thought of as unreachable *)

  | Err_todo of bool * Ast.l * string
  (** [Err_todo] indicates that some feature is unimplemented. Normally,
      it should be build using [err_todo] in order simplify searching
      for occorences in the source code. *)

  | Err_trans of Ast.l * string
  | Err_trans_header of Ast.l * string
  | Err_syntax of Lexing.position * string
  | Err_syntax_locn of Ast.l * string
  | Err_lex of Lexing.position * char
  | Err_type of Ast.l * string
    (** A typechecking error *)
  | Err_internal of Ast.l * string
  | Err_rename of Ast.l * string
  | Err_cyclic_build of string (** resolving module dependencies detected a cyclic dependency of the given module *)
  | Err_cyclic_inline of Ast.l * string * string (** [Err_cyclic_inline l target const] means that the inline of some constant [const] is cyclic for target [target] *)
  | Err_resolve_dependency of Ast.l * string list * string  (** could not find a Module that should be imported in given list of directories *)
  | Err_reorder_dependency of Ast.l * string (** [Err_reorder_dependency (l, m)] module [m] is needed at location [l], but not allowed to be imported, because this
      would require reording the user input *)
  | Err_fancy_pattern_constant of Ast.l * string (** a constant occouring in a pattern has a fancy target-representation, that cannot be dealt with for patterns *)
  
(** Since errors are always fatal, they are reported by raising an [Fatal_error] exception instead of
    calling a report-function. *)
exception Fatal_error of error

(** [err_todo b l m] is an abreviatiation for [Fatal_error (Err_todo (b, l, m))] *)
val err_todo : bool -> Ast.l -> string -> exn

(** [err_general b l m] is an abreviatiation for [Fatal_error (Err_general (b, l, m))] *)
val err_general : bool -> Ast.l -> string -> exn

(** [err_unreachable l m] is an abreviatiation for [Fatal_error (Err_unreachable (l, m))] *)
val err_unreachable : Ast.l -> string -> exn

(** [err_type l msg] is an abreviatiation for [Fatal_error (Err_type (l, m)], i.e. for a general type-checking error
    at location [l] with error message [msg]. *)
val err_type : Ast.l -> string -> exn

(** [err_type l msg pp n] is similar to [err_type]. However it uses the formatter [pp] to format [n], resulting
    in a string [label]. The error message then has the form [label : msg]. *)
val err_type_pp : Ast.l -> string -> (Format.formatter -> 'a -> unit) -> 'a -> exn

(** Report error should only be used by main to print the error in the end. Everywhere else,
    raising a [Fatal_error] exception is recommended. *)
val report_error : error -> 'a


