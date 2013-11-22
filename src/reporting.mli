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

(** reporting errors and warnings *)

(** {2 Warnings } *)

(** Warnings can be caused by definitions or expressions. The type [warm_source] allows
    to pass the origin easily to warnings *)
type warn_source = 
  | Warn_source_exp of Typed_ast.exp
  | Warn_source_def of Typed_ast.def
  | Warn_source_unkown

val warn_source_to_locn : warn_source -> Ast.l

(** Warnings are problems that Lem can deal with. Depending on user settings, they
    can be completely ignored, reported to the user or even be treated as an error. *)
type warning = 
  | Warn_general of bool * Ast.l * string
    (** [Warn_general vl ls m] is a general warning with message [m], locations [ls] and a flag [vl] whether to print these locations verbosely. *)

  | Warn_rename of Ast.l * string * (string * Ast.l) option * string * Target.target 
    (** Warning about renaming an identifier. The arguments are the old name, an optional intermediate one, the new name and the target *)

  | Warn_pattern_compilation_failed of Ast.l * Typed_ast.pat list * warn_source 
    (** pattern compilation failed *)

  | Warn_pattern_not_exhaustive of Ast.l * Typed_ast.pat list list
    (** pattern match is not exhaustive *)

  | Warn_def_not_exhaustive of Ast.l * string * Typed_ast.pat list list
    (** a function is defined using non-exhaustive pattern-matching *) 

  | Warn_pattern_redundant of Ast.l * (int * Typed_ast.pat) list * Typed_ast.exp 
    (** redundant patterns in pattern-match *)

  | Warn_def_redundant of Ast.l * string * (int * Typed_ast.pat) list * Typed_ast.def 
    (** redundant patterns in function definition *)

  | Warn_pattern_needs_compilation of Ast.l * Target.target * Typed_ast.exp * Typed_ast.exp 
    (** [Warn_pattern_needs_compilation l topt old_e new_e] warns about the compilation of [old_e] to [new_e] for target [topt] *)

  | Warn_unused_vars of Ast.l * string list * warn_source 
    (** unused variables detected *)

  | Warn_fun_clauses_resorted of Ast.l * Target.target * string list * Typed_ast.def 
    (** clauses of mutually recursive function definitions resorted *)

  | Warn_record_resorted of Ast.l * Typed_ast.exp
    (** record fields resorted *)

  | Warn_no_decidable_equality of Ast.l * string 
    (** no decidable equality *)

  | Warn_compile_message of Ast.l * Target.target * Path.t * string
    (** [Warn_compile_message (l, target, c, m)] warns using constant [c] form target [target]. *)

  | Warn_import of Ast.l * string * string
    (** [Warn_import (l, module_name, file_name)] warns about auto-importing module [module_name] from [file_name]. *)

  | Warn_overriden_instance of Ast.l * Types.src_t * Types.instance
    (** [Warn_overriden_instance (l, ty, i)] warns that the instance [i] that has already been defined is
        overriden for type [ty] at location [l]. *)

  | Warn_ambiguous_code of Ast.l * string
    (** warn about ambiguous code that could be parsed in several ways and that therefore might confuse users *)


(** if the flag [warnings_active] is set, warning messages are printed, otherwise
    they are thrown away. *)
val warnings_active : bool ref

(** [report_warning env w] reports a warning. Depending on the settings for the warning type this might mean,
    do nothing, print a warning message or print an error message and exit Lem *)
val report_warning : Typed_ast.env -> warning -> unit

(** [report_warning_no_env w] reports a warning, when no-environment is available. 
    In contrast to [report_warning] the warning messages might be more basic, since 
    no information can be extracted from the environment. *)
val report_warning_no_env : warning -> unit

(** {2 Auxiliary Functions } *)

(** Command line options for warnings *)
val warn_opts : (string * Arg.spec * string) list
  
(** Turn off pattern compilation warnings, used by main *)
val ignore_pat_compile_warnings : unit -> unit



(** {2 Debuging } *)

val print_debug_exp : Typed_ast.env -> string -> Typed_ast.exp list -> unit
val print_debug_def : Typed_ast.env -> string -> Typed_ast.def list -> unit
val print_debug_pat : Typed_ast.env -> string -> Typed_ast.pat list -> unit
val print_debug_typ : Typed_ast.env -> string -> Types.t list -> unit
val print_debug_src_t : Typed_ast.env -> string -> Types.src_t list -> unit
