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

(* TODO:
 * 
 * Scoping:
 *   - Catch local hiding of globals for other targets
 *   - Identifier status in HOL
 *
 * Type definitions:
 *   - Mixed abbrevs and datatypes
 *   - type argument ordering
 *   - Semantically well-formed
 * 
 * Definitions:
 *   - Semantically well-formed
 *
 * Relation definitions:
 *   - Semantically well-formed
 *
 * Types:
 *   - Wildcards
 *
 * Expressions:
 *   - Let binding patterns
 *   - Fun binding patterns
 *   - Better operator substitution, esp. for precedence
 *
 * Patterns:
 *   - Record patterns
 *   - As patterns
 * Get rid of before_tyvars and after_tyvars
 *
 *)

open Backend_common
open Typed_ast
open Typed_ast_syntax
open Output
open Target

let gen_extra_level = ref 3

let r = Ulib.Text.of_latin1

let gensym_tex_command =
  let n = ref 0 in
  function () ->
    n := 1 + !n;
    tex_command_escape (Ulib.Text.of_string (string_of_int !n))

(* Use SML-style escape sequences for HOL, with some caveats.  See
 * src/parse/MLstring.sml in HOL source code, as well as
 * http://www.standardml.org/Basis/char.html#SIG:CHAR.toString:VAL *)
let string_escape_hol s =
  let b = Buffer.create (String.length s) in
  let escape_char c = match int_of_char c with
  | 0x5c -> "\\\\" (* backslash *)
  | 0x22 -> "\\\"" (* double quote *)
  | 0x5e -> "^^"   (* carret *)
  | x when x >= 32 && x <= 126 -> (* other printable characters *)
      String.make 1 c
  | 0x07 -> "\\a" (* common control characters *)
  | 0x08 -> "\\b"
  | 0x09 -> "\\t"
  | 0x0a -> "\\n"
  | 0x0b -> "\\v"
  | 0x0c -> "\\f"
  | 0x0d -> "\\r"
  | x when x >= 0 && x < 32 -> (* other control characters *)
      Printf.sprintf "\\^^%c" (char_of_int (x + 64))
  | x when x > 126 && x <= 255 ->
      Printf.sprintf "\\%03u" x
  | _ -> failwith "int_of_char returned an unexpected value"
  in
  (* Do not iterate on the UTF8 code, because HOL does not handle UTF8 even
   * though SML does, for some reason. *)
  String.iter (fun c -> Buffer.add_string b (escape_char c)) s;
  Buffer.contents b

(* Check that string literal s contains only CHR characters for Isabelle.  Other
 * string literals should have been translated into a list by a macro. *)
let string_escape_isa s =
  let is_isa_chr x =
    x >= 0x20 && x <= 0x7e &&
    (* most printable characters are supported, but there are some exceptions! *)
    not (List.mem x [0x22; 0x27; 0x5c; 0x60]) in
  let check_char c =
    if not(is_isa_chr (int_of_char c))
    then raise (Failure "Unsupported character in Isabelle string literal")
  in
  String.iter check_char s; s

module type Target = sig
  val lex_skip : Ast.lex_skip -> Ulib.Text.t
  val need_space : Output.t' -> Output.t' -> bool

  val target : Target.target

  val path_sep : t
  val list_sep : t

  (* Types *)
  val typ_start : t
  val typ_end : t
  val typ_tup_sep : t
  val typ_tup_section : t
  val typ_sep : t
  val typ_fun_sep : t
  val typ_rec_start : t
  val typ_rec_end : t
  val typ_rec_sep : t
  val typ_constr_sep : t
  val typ_var : Ulib.Text.t

  (* Length specifications *)
  val nexp_start : t
  val nexp_end : t
  val nexp_var : Ulib.Text.t
  val nexp_plus : t
  val nexp_times : t

  (* Patterns *)
  val ctor_typ_end : t -> t list -> t
  val ctor_typ_end' : bool -> t -> t list -> t
  val pat_as : t
  val pat_rec_start : t
  val pat_rec_end : t
  val pat_wildcard : t

  (* Constants *)
  val const_true : t
  val const_false : t
  val const_unit : Ast.lex_skips -> t
  val const_empty : Ast.lex_skips -> t
  val string_quote : Ulib.Text.t
  val string_escape : Ulib.UTF8.t -> Ulib.UTF8.t
  val const_num : int -> t
  val const_undefined : Types.t -> string -> t
  val const_bzero : t
  val const_bone : t

  (* Expressions *)
  val case_start : t
  val case_sep1 : t
  val case_sep2 : t
  val case_line_sep : t
  val case_end : t
  val cond_if : t
  val cond_then : t
  val cond_else : t
  val field_access_start : t
  val field_access_end : t
  val fun_start : t
  val fun_end : t
  val fun_kwd : t
  val fun_sep : t
  val function_start : t
  val function_end : t
  val record_assign : t
  val recup_start : t
  val recup_middle : t
  val recup_end : t
  val recup_assign : t
  val val_start : t
  val let_start : t
  val let_in : t
  val let_end : t
  val begin_kwd : t
  val end_kwd : t
  val forall : t
  val exists : t
  val list_quant_binding : t
  val set_quant_binding : t
  val quant_binding_start : t
  val quant_binding_end : t
  val set_start : t
  val set_end : t
  val setcomp_binding_start : t
  val setcomp_binding_sep : t
  val setcomp_binding_middle : t
  val setcomp_sep : t
  val cons_op : t
  val pat_add_op : t
  val set_sep : t
  val list_begin : t
  val list_end : t
  val vector_begin : t
  val vector_end : t
  val first_case_sep : (Ast.lex_skips,t) Seplist.optsep
  val op_format : bool -> Output.id_annot -> Ulib.Text.t -> t

  (* Pattern and Expression tuples *)
  val tup_sep : t

  (* Value definitions *)
  val def_start : t
  val def_binding : t
  val def_end : t
  val def_sep : t
  val name_start : t
  val name_end : t
  val rec_def_header : bool -> bool -> lskips -> lskips -> Name.t -> t
    (** [rec_def_header is_rec is_real_rec sk1 sk2 n] formats [let sk1 rec? sk2 n]. 
        The flag [is_rec] denotes whether the keyword [rec] occours in the input, while
        [is_real_rec] denotes whether the definition is really recursive. *)
  val rec_def_footer : bool -> bool -> Name.t -> t
  val funcase_start : t
  val funcase_end : t
  val reln_start : t
  val reln_end : t
  val reln_sep : t
  val reln_name_start : t
  val reln_name_end : t
  val reln_clause_start : t
  val reln_clause_quant : t
  val reln_clause_show_empty_quant : bool
  val reln_clause_show_name : bool
  val reln_clause_quote_name : bool
  val reln_clause_add_paren : bool
  val reln_clause_end : t

  (* Type defnitions *)
  val typedef_start : t
  val typedef_binding : t
  val typedef_end : t
  val typedef_sep : t
  val typedefrec_start : t
  val typedefrec_end : t

  val rec_start : t
  val rec_end : t
  val rec_sep : t
  val constr_sep : t
  val before_tyvars : t
  val after_tyvars : t
  val last_rec_sep : (Ast.lex_skips,t) Seplist.optsep
  val last_list_sep : (Ast.lex_skips,t) Seplist.optsep
  val last_set_sep : (Ast.lex_skips,t)Seplist.optsep 
  val first_variant_sep : (Ast.lex_skips,t) Seplist.optsep
  val type_params_pre : bool
  val nexp_params_vis : bool
  val type_abbrev_start : t
  val type_abbrev_sep : t
  val type_abbrev_end : t
  val type_abbrev_name_quoted : bool

  (* modules *)
  val module_module : t
  val module_struct : t
  val module_end : t
  val module_open : t
  val module_import : t



  (* TODO: remove some and none *)
  val some : Ident.t
  val none : Ident.t
  val inl : Ident.t
  val inr : Ident.t
end


module Identity : Target = struct
  open Str

  let lex_skip = function
    | Ast.Com(r) -> ml_comment_to_rope r
    | Ast.Ws(r) -> r
    | Ast.Nl -> r"\n"

  module S = Set.Make(String)

  let delim_regexp = regexp "^\\([][`;,(){}]\\|;;\\)$"

  let symbolic_regexp = regexp "^[-!$%&*+./:<=>?@^|~]+$"

  let is_delim s = 
    string_match delim_regexp s 0

  let is_symbolic s = 
    string_match symbolic_regexp s 0

  let need_space x y = 
    let f x =
      match x with
        | Kwd'(s) ->
            if is_delim s then
              (true,false)
            else if is_symbolic s then
              (false,true)
            else
              (false,false)
        | Ident'(r) ->
            (false, is_symbolic (Ulib.Text.to_string r))
        | Num' _ ->
            (false,false)
    in
    let (d1,s1) = f x in
    let (d2,s2) = f y in
      not d1 && not d2 && s1 = s2

  let target = Target_ident

  let path_sep = kwd "."
  let list_sep = kwd ";"

  let ctor_typ_end _ _ = emp
  let ctor_typ_end' _ _ _ = emp

  let typ_start = emp
  let typ_end = emp
  let typ_tup_sep = kwd "*"
  let typ_tup_section = emp
  let typ_sep = kwd ":"
  let typ_fun_sep = kwd "->"
  let typ_rec_start = kwd "<|"
  let typ_rec_end = kwd "|>"
  let typ_rec_sep = kwd ";"
  let typ_constr_sep = kwd "of"
  let typ_var = r"'"

  let nexp_start = emp
  let nexp_end = emp
  let nexp_var = r"''"
  let nexp_plus = kwd "+"
  let nexp_times = kwd "*"
  
  let pat_as = kwd "as"
  let pat_rec_start = kwd "<|"
  let pat_rec_end = kwd "|>"
  let pat_wildcard = kwd "_"

  let const_true = kwd "true"
  let const_false = kwd "false"
  let const_unit s = kwd "(" ^ ws s ^ kwd ")"
  let const_empty s = kwd "{" ^ ws s ^ kwd "}"
  let string_quote = r"\""
  let string_escape = String.escaped
  let const_num = num
  let const_undefined t m = (kwd "Undef") (* ^ (comment m) *)
  let const_bzero = kwd "#0"
  let const_bone = kwd "#1"

  let case_start = kwd "match"
  let case_sep1 = kwd "with"
  let case_sep2 = kwd "|"
  let case_line_sep = kwd "->"
  let case_end = kwd "end"
  let cond_if = kwd "if"
  let cond_then = kwd "then"
  let cond_else = kwd "else"
  let field_access_start = kwd "."
  let field_access_end = emp
  let fun_start = emp
  let fun_end = emp
  let fun_kwd = kwd "fun"
  let fun_sep = kwd "->"
  let function_start = kwd "function"
  let function_end = kwd "end"
  let record_assign = kwd "="
  let recup_start = kwd "<|"
  let recup_middle = kwd "with"
  let recup_end = kwd "|>"
  let recup_assign = kwd "="
  let val_start = kwd "val"
  let let_start = kwd "let"
  let let_in = kwd "in"
  let let_end = emp
  let begin_kwd = kwd "begin"
  let end_kwd = kwd "end"
  let forall = kwd "forall"
  let exists = kwd "exists"
  let set_quant_binding = kwd "IN"
  let list_quant_binding = kwd "MEM"
  let quant_binding_start = kwd "("
  let quant_binding_end = kwd ")"
  let set_start = kwd "{"
  let set_end = kwd "}"
  let setcomp_binding_start = kwd "forall"
  let setcomp_binding_sep = emp
  let setcomp_binding_middle = kwd "|"
  let setcomp_sep = kwd "|"
  let cons_op = kwd "::"
  let pat_add_op = kwd "+"
  let set_sep = kwd ";"
  let list_begin = kwd "["
  let list_end = kwd "]"
  let vector_begin = kwd "[|"
  let vector_end = kwd "|]"
  let first_case_sep = Seplist.Optional

  let tup_sep = kwd ","

  let star = Ulib.Text.of_latin1 "*"
  let space = Output.ws (Some [Ast.Ws (Ulib.Text.of_latin1 " ")])
  let infix_op_format a x =
     if (Ulib.Text.left x 1 = star || Ulib.Text.right x 1 = star) then
       kwd "(" ^ space ^ id a x ^ space ^ kwd ")"
     else
       kwd "(" ^ id a x ^ kwd ")"

  let op_format use_infix = if use_infix then infix_op_format else id

  let def_start = kwd "let"
  let def_binding = kwd "="
  let def_end = emp
  let def_sep = kwd "and"
  let name_start = kwd "["
  let name_end = kwd "]"
  let rec_def_header rr rrr sk1 sk2 _ =  ws sk1 ^ kwd "let" ^ ws sk2 ^ (if (rr || rrr) then kwd "rec" else emp)
  let rec_def_footer _ _ n = emp
  let funcase_start = emp
  let funcase_end = emp
  let reln_start = kwd "indreln"
  let reln_end = emp
  let reln_sep = kwd "and"
  let reln_name_start = kwd "["
  let reln_name_end = kwd "]"
  let reln_clause_quant = kwd "forall"
  let reln_clause_show_empty_quant = true
  let reln_clause_show_name = true
  let reln_clause_quote_name = false
  let reln_clause_add_paren = false
  let reln_clause_start = emp
  let reln_clause_end = emp

  let typedef_start = kwd "type"
  let typedef_binding = kwd "="
  let typedef_end = emp
  let typedef_sep = kwd "and"
  let typedefrec_start = kwd "type"
  let typedefrec_end = emp
  let typedefrec_implicits _ = emp
  let rec_start = kwd "<|"
  let rec_end = kwd "|>"
  let rec_sep = kwd ";"
  let constr_sep = kwd "*"
  let before_tyvars = emp
  let after_tyvars = emp
  let type_abbrev_start = kwd "type"
  let last_rec_sep = Seplist.Optional
  let last_list_sep = Seplist.Optional
  let last_set_sep = Seplist.Optional
  let first_variant_sep = Seplist.Optional
  let type_params_pre = false
  let nexp_params_vis = true
  let type_abbrev_sep = kwd "="
  let type_abbrev_end = emp
  let type_abbrev_name_quoted = false
  let module_module = kwd "module"
  let module_struct = kwd "struct"
  let module_end = kwd "end"
  let module_open = kwd "open"
  let module_import = kwd "import"

  let some = Ident.mk_ident_strings [] "Some"
  let none = Ident.mk_ident_strings [] "None"
  let inl = Ident.mk_ident_strings [] "Inl"
  let inr = Ident.mk_ident_strings [] "Inr"
end

module Html : Target = struct
  include Identity 
  let target = Target_no_ident Target_html

  let forall = kwd "&forall;"
  let exists = kwd "&exist;"
  let set_quant_binding = kwd "&isin;"
  let setcomp_binding_start = kwd "&forall;"
  let reln_clause_quant = kwd "&forall;"
  let reln_clause_show_empty_quant = true
  let reln_clause_show_name = true
  let reln_clause_quote_name = false
  let reln_clause_add_paren = false
  let reln_clause_start = emp

end

module Tex : Target = struct
  open Str

  let lex_skip = function _ -> r"DUMMY"

  module S = Set.Make(String)

  let delim_regexp = regexp "^\\([][`;,(){}]\\|;;\\)$"

  let symbolic_regexp = regexp "^[-!$%&*+./:<=>?@^|~]+$"

  let is_delim s = 
    string_match delim_regexp s 0

  let is_symbolic s = 
    string_match symbolic_regexp s 0

  let need_space x y = false

  let target = Target_no_ident Target_tex

  let tkwd s = kwd (String.concat "" ["\\lemkw{"; s;  "}"])
  let tkwdl s = kwd (String.concat "" ["\\lemkw{"; s;  "}"]) ^ texspace
  let tkwdr s = texspace ^ kwd (String.concat "" ["\\lemkw{"; s;  "}"]) 
  let tkwdm s = texspace ^ kwd (String.concat "" ["\\lemkw{"; s;  "}"]) ^ texspace

  let path_sep = kwd "." (* "`" *)
  let list_sep = kwd ";"

  let const_unit s = kwd "(" ^ ws s ^ kwd ")"
  let const_empty s = kwd "\\{" ^ ws s ^ kwd "\\}"

  let ctor_typ_end _ _ = emp
  let ctor_typ_end' _ _ _ = emp

  let typ_start = emp
  let typ_end = emp
  let typ_tup_sep = kwd "*"
  let typ_tup_section = emp
  let typ_sep = kwd ":"
  let typ_fun_sep = kwd "\\rightarrow "
  let typ_rec_start = kwd "\\Mmagiclrec"
  let typ_rec_end = kwd "\\Mmagicrrec "
  let typ_rec_sep = kwd ";\\,"
  let typ_constr_sep = tkwdm "of"
  let typ_var = r"'"
  
  let nexp_start = emp
  let nexp_end = emp
  let nexp_var = r"''"
  let nexp_plus = kwd "+"
  let nexp_times = kwd "*"

  let pat_as = tkwd "as"
  let pat_rec_start = kwd "\\Mmagiclrec"
  let pat_rec_end = kwd "\\Mmagicrrec"
  let pat_wildcard = kwd "\\_"

  let const_true = tkwd "true"
  let const_false = tkwd "false"
  let string_quote = r"\""
  let string_escape = String.escaped
  let const_num = num
  let const_undefined t m = (tkwd "undefined")
  let const_bzero = kwd "#0"
  let const_bone = kwd "#1"

  let case_start = tkwdl "match"
  let case_sep1 = tkwdm "with"
  let case_sep2 = kwd "|" ^ texspace
  let case_line_sep = kwd "\\rightarrow"
  let case_end = tkwdr "end"
  let cond_if = tkwdl "if"
  let cond_then = tkwdm "then"
  let cond_else = tkwdm "else"
  let field_access_start = kwd "."
  let field_access_end = emp
  let fun_start = emp
  let fun_end = emp
  let fun_kwd = tkwdl "fun"
  let fun_sep = kwd "\\rightarrow"
  let function_start = tkwdl "function"
  let function_end = tkwdr "end"
  let record_assign = kwd "="
  let recup_start = kwd "\\Mlrec"
  let recup_middle = texspace ^ kwd "\\Mmagicwith" ^ texspace 
  let recup_end = kwd "\\Mmagicrrec"
  let recup_assign = kwd "="
  let rec_literal_start = kwd "\\Mmagiclrec"
  let rec_literal_end = kwd "\\Mmagicrrec "
  let rec_literal_sep = kwd ";\\,"
  let rec_literal_assign = kwd "="
  let val_start = tkwdl "val"
  let let_start = tkwdl "let"
  let let_in = tkwdm "in"
  let let_end = emp
  let begin_kwd = tkwdl "begin"
  let end_kwd = tkwdr "end"
  let forall = kwd "\\forall"
  let exists = kwd "\\exists"
  let set_quant_binding = kwd "\\mathord{\\in} "
  let list_quant_binding = tkwdm "mem"
  let quant_binding_start = emp (* kwd "("*)
  let quant_binding_end = emp (* kwd ")"*)
  let set_start = kwd "\\{"
  let set_end = kwd "\\}"
  let setcomp_binding_start = kwd "\\forall"
  let setcomp_binding_sep = emp
  let setcomp_binding_middle = texspace ^ kwd "|" ^ texspace
  let setcomp_sep = texspace ^ kwd "|" ^ texspace
  let cons_op = kwd "::"
  let pat_add_op = kwd "+"
  let set_sep = kwd ";\\,"
  let list_begin = kwd "["
  let list_end = kwd "]"
  let vector_begin = kwd "[|"
  let vector_end = kwd "|]"
  let first_case_sep = Seplist.Optional
  let op_format = Identity.op_format

  let tup_sep = kwd ",\\,"

  let def_start = tkwdl "let"
  let def_binding = kwd "="
  let def_end = emp
  let name_start = kwd "["
  let name_end = kwd "]"
  let def_sep = kwd "|"
  let rec_def_header _ rrr sk1 sk2 _ = ws sk1 ^ tkwdm "let" ^ ws sk2 ^ (if rrr then tkwdm "rec" else emp)
  let rec_def_footer _ _ n = emp
  let funcase_start = emp
  let funcase_end = emp
  let reln_start = tkwdl "indreln"
  let reln_end = emp
  let reln_sep = tkwdm "and"
  let reln_name_start = kwd "["
  let reln_name_end = kwd "]"
  let reln_clause_start = emp
  let reln_clause_quant = kwd "\\forall"
  let reln_clause_show_empty_quant = true
  let reln_clause_show_name = true
  let reln_clause_quote_name = false
  let reln_clause_add_paren = false
  let reln_clause_end = emp

  let typedef_start = tkwdl "type"
  let typedef_binding = kwd "="
  let typedef_end = emp
  let typedef_sep = tkwdm "and"
  let typedefrec_start = tkwdl "type"
  let typedefrec_end = emp
  let typedefrec_implicits _ = emp
  let rec_start = kwd "\\Mmagiclrec"
  let rec_end = kwd "\\Mmagicrrec"
  let rec_sep = kwd ";"
  let constr_sep = kwd "*"
  let before_tyvars = emp
  let after_tyvars = emp
  let type_abbrev_start = tkwdl "type"
  let last_rec_sep = Seplist.Optional
  let last_list_sep = Seplist.Optional
  let last_set_sep = Seplist.Optional
  let first_variant_sep = Seplist.Optional
  let type_params_pre = false
  let nexp_params_vis = true
  let type_abbrev_sep = kwd "="
  let type_abbrev_end = emp
  let type_abbrev_name_quoted = false

  let module_module = tkwdl "module"
  let module_struct = tkwdl "struct"
  let module_end = tkwdr "end"
  let module_open = tkwdl "open"
  let module_import = tkwdl "import"

  let some = Ident.mk_ident_strings [] "Some"
  let none = Ident.mk_ident_strings [] "None"
  let inl = Ident.mk_ident_strings [] "Inl"
  let inr = Ident.mk_ident_strings [] "Inr"
end


module Ocaml : Target = struct
  include Identity 

  let target = Target_no_ident Target_ocaml

  let path_sep = kwd "."

  let typ_rec_start = kwd "{"
  let typ_rec_end = kwd "}"
  let nexp_start = kwd "(*"
  let nexp_end = kwd "*)"
  let nexp_var = r""

  let ctor_typ_end _ _ = emp
  let ctor_typ_end' _ _ _ = emp

  let pat_rec_start = kwd "{"
  let pat_rec_end = kwd "}"
  let pat_wildcard = kwd "_"

  let pat_add_op = err "add pattern in Ocaml"

  let function_start = kwd "(" ^ kwd "function"
  let function_end = kwd ")"
  let case_start = kwd "(" ^ kwd "match"
  let case_end = kwd ")"
  let recup_start = kwd "{"
  let recup_end = kwd "}"
  let vector_begin = kwd "(" ^ kwd "Vector.Vector" ^ kwd "[|"
  let vector_end = kwd "|]" ^ kwd ")"
  let const_bzero = kwd "Bit.Zero"
  let const_bone = kwd "Bit.One"

  let rec_start = kwd "{"
  let rec_end = kwd "}"

  let def_sep = kwd "and"
  let name_start = kwd "(*"
  let name_end = kwd "*)"
  let type_params_pre = true
  let nexp_params_vis = false
  
  let inl = Ident.mk_ident_strings [] "Inl"
  let inr = Ident.mk_ident_strings [] "Inr"
end

let back_tick = List.hd (Ulib.Text.explode (r"`"))
let quotation_mark = List.hd (Ulib.Text.explode (r"\""))
let backslash = List.hd (Ulib.Text.explode (r"\\"))

module Isa : Target = struct
  include Identity 

  let lex_skip = function
    | Ast.Com(r) ->
      Ulib.Text.filter (fun c -> not(c = quotation_mark) && not (c=backslash)) (ml_comment_to_rope r)
    | Ast.Ws(r) -> r
    | Ast.Nl -> r"\n"

  let target = Target_no_ident Target_isa

  (* TODO : write need_space *)

  let path_sep = kwd "."
  let list_sep = kwd ","

  let ctor_typ_end _ _ = emp
  let ctor_typ_end' _ _ _ = emp

  let typ_start = kwd "\""
  let typ_end = kwd "\""
  let typ_tup_sep = kwd "*"
  let typ_tup_section = emp
  let typ_sep = kwd "::"
  let typ_fun_sep = kwd " => "
  let typ_rec_start = kwd "\n"
  let typ_rec_end = kwd "\n"
  let typ_rec_sep = kwd "\n"
  let typ_constr_sep = emp
  let typ_var = r"'"

  let pat_as = err "as pattern in Isabelle"
  let pat_rec_start = err "record pattern in Isabelle"
  let pat_rec_end = err "record pattern in Isabelle"

  let const_true = kwd "True"
  let const_false = kwd "False"
  let string_quote = r"''"
  let string_escape = string_escape_isa
  let const_num i = kwd "(" ^  num i ^ kwd ":: nat)"
  let const_unit s = kwd "() " ^ ws s
  let const_empty s = kwd "{} " ^ ws s
  let const_undefined t m = (kwd "undefined")
  let const_bzero = emp
  let const_bone = emp

  let case_start = kwd "(case "
  let case_sep1 = kwd "of"
  let case_sep2 = kwd "|"
  let case_line_sep = kwd "=>"
  let case_end = kwd ")"

  let field_access_start = emp
  let field_access_end = kwd " "
  
  let fun_start = kwd "("
  let fun_end = kwd ")"
  let fun_kwd = kwd "%"
  let fun_sep = kwd ". "

  let record_assign = kwd "="
  let recup_start = emp
  let recup_middle = kwd "(|"
  let recup_end = kwd "|)"
  let recup_assign = kwd ":="

  let val_start = kwd "val" (* TODO*)
  let let_start = kwd "(" ^ kwd "let"
  let let_end = kwd ")"

  let begin_kwd = kwd "("
  let end_kwd = kwd ")"
  
  let forall = kwd "ALL"
  let exists = kwd "EX"

  let set_quant_binding = kwd ":"
  let quant_binding_start = emp
  let quant_binding_end = emp

  let set_start = kwd "{"
  let set_end = kwd "}"
  let setcomp_binding_start = emp
  let setcomp_binding_sep = kwd " "
  let setcomp_binding_middle = kwd "."
  let setcomp_sep = kwd "|"
  let first_case_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let infix_op_format a x = match a with (Term_var | Term_var_toplevel) -> id a x | _ -> kwd "(op" ^ id a x  ^ kwd ")"

  let op_format use_infix = if use_infix then infix_op_format else id

  let pat_add_op = err "add pattern in Isabelle"
  let cons_op = kwd "#"
  let set_sep = kwd ","

  let def_start = kwd "definition"
  let def_end = emp

  let def_sep = kwd "|"
  let rec_def_header _ rr sk1 sk2 _ = (if rr then kwd "function (sequential)" else kwd "fun") ^ ws sk1 ^ ws sk2
  let rec_def_footer _ rr n = if rr then kwd "by pat_completeness auto" else emp
  
  let funcase_start = emp
  let funcase_end = emp
  let reln_start = kwd "inductive"
  let reln_end = emp
  let reln_sep = kwd "|"
  let reln_name_start = emp (*TODO Indreln fix up for isabelle*)
  let reln_name_end = emp
  let reln_clause_start = kwd "\""
  let reln_clause_quant = kwd "!!"
  let reln_clause_show_empty_quant = false
  let reln_clause_show_name = true
  let reln_clause_quote_name = true
  let reln_clause_add_paren = false
  let reln_clause_end = kwd "\""

  let typedef_start = kwd "datatype"
  let typedef_end = emp
  let typedef_sep = kwd "and"

  let typedefrec_start = kwd "record"
  let typedefrec_end = emp
  let rec_start = kwd "(|"
  let rec_end = kwd "|)"
  let rec_sep = kwd ","

  let constr_sep = kwd "\" \""
  let before_tyvars = emp
  let after_tyvars = emp
  let first_variant_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let last_list_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let last_rec_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let last_set_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let type_abbrev_start = kwd "type_synonym"
  let type_abbrev_sep = kwd "="
  let type_abbrev_end = emp

  let type_params_pre = true
  let nexp_params_vis = false

end

module Hol : Target = struct
  open Str

  let lex_skip = function
    | Ast.Com(r) -> 
        (*
        Ulib.Text.replace 
          (fun c -> 
             if c = back_tick then 
               (* TODO: Use ^` instead? *)
               Ulib.Text.to_ustring (r"REPLACED BACKQUOTE") 
             else 
               BatUTF8.of_char c)
         *)
          (ml_comment_to_rope r)
    | Ast.Ws(r) -> r
    | Ast.Nl -> r"\n"

  (* TODO: These join up :- -> *, *)
  let delim_regexp = regexp "^\\([][(){}~.,;-]\\)$"

  let symbolic_regexp = regexp "^[!%&*+/:<=>?@^|#\\`]+$"

  let is_delim s = 
    string_match delim_regexp s 0

  let is_symbolic s = 
    string_match symbolic_regexp s 0

  let need_space x y = 
    let f x =
      match x with
        | Kwd'(s) ->
            if is_delim s then
              (true,false)
            else if is_symbolic s then
              (false,true)
            else
              (false,false)
        | Ident'(r) ->
            (false, is_symbolic (Ulib.Text.to_string r))
        | Num' _ ->
            (false,false)
    in
    let (d1,s1) = f x in
    let (d2,s2) = f y in
      not d1 && not d2 && s1 = s2

  let target = Target_no_ident Target_hol

  let path_sep = meta "$"
  let list_sep = kwd ";"

  let ctor_typ_end _ _ = emp
  let ctor_typ_end' _ _ _ = emp

  let typ_start = emp
  let typ_end = emp
  let typ_tup_sep = kwd "#"
  let typ_tup_section = emp
  let typ_sep = kwd ":"
  let typ_fun_sep = kwd "->"
  let typ_rec_start = kwd "<|"
  let typ_rec_end = kwd "|>"
  let typ_rec_sep = kwd ";"
  let typ_constr_sep = kwd "of"
  let typ_var = r"'"

  let nexp_start = kwd "(*"
  let nexp_end = kwd "*)"
  let nexp_var = r"'" (* Currently turning into standard type variable, shouldn't appear in source *)
  let nexp_plus = emp
  let nexp_times = emp


  let pat_as = err "as pattern in HOL"
  let pat_rec_start = err "record pattern in HOL"
  let pat_rec_end = err "record pattern in HOL"
  let pat_wildcard = kwd "_"

  let const_true = kwd "T"
  let const_false = kwd "F"
  let const_unit s = kwd "() " ^ ws s
  let const_empty s = kwd "{" ^ ws s ^ kwd "}"
  let string_quote = r"\""
  let string_escape = string_escape_hol
  let const_num = num
  let const_undefined t m = (kwd "ARB") 
  let const_bzero = emp
  let const_bone = emp

  let function_start = err "function in HOL"
  let function_end = err "function in HOL"
  let case_start = kwd "(" ^ kwd "case"
  let case_sep1 = kwd "of"
  let case_sep2 = kwd "|"
  let case_line_sep = kwd "=>"
  let case_end = kwd ")"
  let cond_if = kwd "if"
  let cond_then = kwd "then"
  let cond_else = kwd "else"
  let field_access_start = kwd "."
  let field_access_end = emp
  let fun_start = emp
  let fun_end = emp
  let fun_kwd = kwd "\\"
  let fun_sep = kwd "."
  let record_assign = kwd ":="
  let recup_start = kwd "("
  let recup_middle = kwd "with" ^ kwd "<|"
  let recup_end = kwd "|>" ^ kwd ")"
  let recup_assign = kwd ":="
  let val_start = err "val specification in HOL"
  let let_start = kwd "let"
  let let_in = kwd "in"
  let let_end = emp
  let begin_kwd = kwd "("
  let end_kwd = kwd ")"
  let forall = kwd "!"
  let exists = kwd "?"
  let list_quant_binding = err "list restricted quantifier in HOL"
  let set_quant_binding = kwd "::"
  let quant_binding_start = kwd "("
  let quant_binding_end = kwd ")"
  let set_start = kwd "{"
  let set_end = kwd "}"
  let setcomp_binding_start = emp
  let setcomp_binding_sep = kwd ","
  let setcomp_binding_middle = kwd "|"
  let setcomp_sep = kwd "|"
  let pat_add_op = err "add pattern in Hol"
  let cons_op = kwd "::"
  let set_sep = kwd ";"
  let list_begin = kwd "["
  let list_end = kwd "]"
  let vector_begin = emp
  let vector_end = emp
  let first_case_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let infix_op_format a x = match a with (Term_var | Term_var_toplevel) -> id a x | _ -> kwd "(" ^ (id a x) ^ kwd ")"
  let op_format use_infix = if use_infix then infix_op_format else id

  let tup_sep = kwd ","

  let def_start = meta "val _ = Define `\n"
  let def_binding = kwd "="
  let def_end = meta "`;\n"
  let def_sep = kwd "/\\"
  let name_start = kwd "(*"
  let name_end = kwd "*)"
  let rec_def_header _ rrr sk1 sk2 n = 
    ws sk1 ^ ws sk2 ^   
    let n = Ulib.Text.to_string (Name.to_rope n) in 
      if rrr then
        meta (Format.sprintf "val %s_defn = Hol_defn \"%s\" `\n" n n)
      else
        meta (Format.sprintf "val _ = Define `\n")
  let rec_def_footer _ rrr n =
     if rrr then
       meta (Format.sprintf "\nval _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn %s_defn;" 
            (Ulib.Text.to_string (Name.to_rope n)))
     else emp

  let funcase_start = kwd "("
  let funcase_end = kwd ")"
  let reln_start = meta "val _ = Hol_reln `"
  let reln_end = meta "`;"
  let reln_sep = kwd "/\\"
  let reln_name_start = emp (*TODO Inderln fixup for Hol*)
  let reln_name_end = emp
  let reln_clause_start = kwd "("
  let reln_clause_quant = kwd "!"
  let reln_clause_show_empty_quant = false
  let reln_clause_show_name = false
  let reln_clause_quote_name = false
  let reln_clause_add_paren = true
  let reln_clause_end = kwd ")"

  let typedef_start = meta "val _ = Hol_datatype `\n"
  let typedef_binding = kwd "="
  let typedef_end = meta "`;\n"
  let typedef_sep = kwd ";"
  let typedefrec_start = meta "val _ = Hol_datatype `\n"
  let typedefrec_end = meta "`;\n"
  let typedefrec_implicits _ = emp
  let rec_start = kwd "<|"
  let rec_end = kwd "|>"
  let rec_sep = kwd ";"
  let constr_sep = kwd "=>"
  let before_tyvars = kwd "(*" ^ space
  let after_tyvars = space ^ kwd "*)"
  let last_rec_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let last_list_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let last_set_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let first_variant_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let type_params_pre = true
  let nexp_params_vis = false
  let type_abbrev_start = meta "val _ = type_abbrev("
  let type_abbrev_sep = meta ", ``:"
  let type_abbrev_end = meta "``);"
  let type_abbrev_name_quoted = true

  let module_module = kwd "module"
  let module_struct = kwd "struct"
  let module_end = kwd "end"
  let module_open = kwd "open"
  let module_import = kwd "import"

  let some = Ident.mk_ident_strings [] "SOME"
  let none = Ident.mk_ident_strings [] "NONE"
  let inl = Ident.mk_ident_strings [] "INL"
  let inr = Ident.mk_ident_strings [] "INR"
end


(* which extra information should be generated? *)
type extra_gen_flags = 
   {extra_gen_termination: bool; 
    extra_gen_asserts: bool;
    extra_gen_lemmata: bool;
    extra_gen_theorems: bool;
};;

let extra_gen_flags_gen_lty (gf : extra_gen_flags) = function
  | Ast.Lemma_theorem _ -> gf.extra_gen_theorems
  | Ast.Lemma_lemma _ -> gf.extra_gen_lemmata
  | Ast.Lemma_assert _ -> gf.extra_gen_asserts


module F_Aux(T : Target)(A : sig val avoid : var_avoid_f option;; val env : env;; val ascii_rep_set : Types.Cdset.t end)(X : sig val comment_def : def -> Ulib.Text.t end) = struct

module B = Backend_common.Make (struct
  let env = A.env
  let target = T.target
  let id_format_args =  (T.op_format, T.path_sep)    
end);;

module C = Exps_in_context (struct
  let env_opt = Some A.env
  let avoid = A.avoid
end);;

let use_ascii_rep_for_const (cd : const_descr_ref id) : bool = Types.Cdset.mem cd.descr A.ascii_rep_set

let rec interspace os = 
  match os with
  | [] -> [emp]
  | [x] -> [x]
  | x::((_::_) as os') -> x:: texspace:: interspace os'

let sep x s = ws s ^ x

(*Bracket with s a list of types, tnvars, etc, but omit the s on a match *)
let bracket_omit f omit_match alter_init_skips s b1 b2 l =
  let rec all l = match l with
     | [] -> emp
     | [t] -> f t
     | (t::ts) -> (omit_match t f s) ^ all ts
  in 
  match l with
    | [] -> emp
    | [t] -> f t
    | (t::ts) ->
       (* Put the parnthesis right before the first type *)
       let (t',sk) = alter_init_skips (fun (s) -> (None,s)) t in
       ws sk ^ b1 ^ all (t'::ts) ^ b2

let bracket_many f s b1 b2 l =
  match l with
    | [] -> emp
    | [t] -> f t
    | (t::ts) -> 
        (* Put the parenthesis right before the first type *)
        let (t', sk) = typ_alter_init_lskips (fun (s) -> (None,s)) t in
          ws sk ^ b1 ^ concat s (List.map f (t'::ts))  ^ b2

let lit l t = match l.term with
  | L_true(s) -> ws s ^ T.const_true
  | L_false(s) -> ws s ^ T.const_false
  | L_undefined(s,m) -> ws s ^ T.const_undefined t m
  | L_num(s,i) -> ws s ^ T.const_num i
  | L_string(s,i) -> ws s ^ str (Ulib.Text.of_string (T.string_escape i))
  | L_unit(s1,s2) -> ws s1 ^ T.const_unit s2
  | L_zero(s) -> ws s ^ T.const_bzero 
  | L_one(s) -> ws s ^ T.const_bone
  | L_vector(s,p,b) -> ws s ^ kwd (String.concat "" [p;b])

let nexp n =
  let rec nexp_int n = match n.nterm with
    | Nexp_var(s,v) ->
        ws s ^ id Nexpr_var (Ulib.Text.(^^^) T.nexp_var (Nvar.to_rope v))
    | Nexp_const(s,i) ->
        ws s ^ T.const_num i
    | Nexp_mult(n1,s,n2) ->
        nexp_int n1 ^ ws s ^ T.nexp_times ^ nexp_int n2
    | Nexp_add(n1,s,n2) ->
        nexp_int n1 ^ ws s ^ T.nexp_plus ^ nexp_int n2 
    | Nexp_paren(s1,n,s2) ->
        ws s1 ^ kwd "(" ^ nexp_int n ^ ws s2 ^ kwd ")"
  in T.nexp_start ^ nexp_int n ^ T.nexp_end

let rec typ t = match t.term with
  | Typ_wild(s) ->
      ws s ^ kwd "_"
  | Typ_var(s,v) ->
      ws s ^ id Type_var (Ulib.Text.(^^^) T.typ_var (Tyvar.to_rope v))
  | Typ_fn(t1,s,t2) ->
      typ t1 ^
      ws s ^
      T.typ_fun_sep ^
      typ t2
  | Typ_tup(ts) ->
      flat (Seplist.to_sep_list typ (sep T.typ_tup_sep) ts) ^ T.typ_tup_section
  | (Typ_app(p, ts) | Typ_backend(p, ts)) ->
      let p_out = begin 
        let i = match t.term with
          | Typ_app _ -> B.type_id_to_ident p
          | Typ_backend _ -> B.type_id_to_ident_no_modify p
          | _ -> raise (Reporting_basic.err_unreachable (Ast.Trans (false, "Backend.typ", None)) "can't be reached because of previous match")
        in
        Ident.to_output Type_ctor T.path_sep i
      end in
      if (T.type_params_pre) then
        if (T.nexp_params_vis) then
          bracket_many typ (T.tup_sep) (kwd "(") (kwd ")") ts ^
          texspace ^ p_out
        else 
          bracket_omit typ (fun t f s -> match t.term with 
                                        | Typ_len _ -> f t
                                        | _ -> f t ^ s) typ_alter_init_lskips (T.tup_sep) (kwd "(") (kwd ")") ts ^
          texspace ^ p_out
      else
        p_out ^
        texspace ^
        concat emp (List.map typ ts)
  | Typ_len(n) -> nexp n
  | Typ_paren(s1,t,s2) ->
      ws s1 ^
      kwd "(" ^
      typ t ^
      ws s2 ^
      kwd ")"

let field_ident_to_output cd =
  Ident.to_output Term_field T.path_sep (B.const_id_to_ident cd (use_ascii_rep_for_const cd))
;;

let tyvar tv =
  match tv with
   | Tn_A(s,tv,l) -> ws s ^ id Type_var (Ulib.Text.(^^^) T.typ_var tv)
   | Tn_N(s,nv,l) -> ws s ^ id Nexpr_var (Ulib.Text.(^^^) T.nexp_var nv)

let tyfield ((n,l),f_ref,s1,t) =
  Name.to_output Term_field (B.const_ref_to_name n false f_ref) ^
  ws s1 ^
  block false 2 ( 
  T.typ_sep ^
  T.typ_start ^
  block false 0 (typ t) ^
  T.typ_end)

let tyconstr implicit n' tvs ((n,l),c_ref,s1,targs) =
  Name.to_output Type_ctor (B.const_ref_to_name n false c_ref) ^
  ws s1 ^
  (if Seplist.length targs = 0 then
     T.ctor_typ_end n' tvs
   else
     T.typ_constr_sep ^
     T.typ_start ^
     flat (Seplist.to_sep_list typ (sep T.constr_sep) targs) ^
     T.ctor_typ_end' implicit n' tvs ^
     T.typ_end ^
     break_hint_space 0 )

let tyexp_abbrev s4 t =
  ws s4 ^
  T.type_abbrev_sep ^
  T.typ_start ^
  typ t ^
  T.typ_end

let tyexp_rec s4 s5 fields s6 =
  ws s4 ^
  T.typedef_binding ^
  ws s5 ^  
  block false 2 (
  break_hint_space 2 ^
  T.typ_rec_start ^
  block_hv false 0 (
  flat (Seplist.to_sep_list_last 
          T.last_rec_sep 
          tyfield (sep (T.typ_rec_sep ^ break_hint_space 0)) fields) ^
  ws s6) ^ 
  T.typ_rec_end)

let tyexp implicit n tvs = function
  | Te_opaque -> 
      emp
  
  | Te_abbrev(s,t) ->
      tyexp_abbrev s t
  
  | Te_record(s3, s1, fields, s2) ->
      tyexp_rec s3 s1 fields s2
 
  | Te_variant(s,constrs) ->
      ws s ^
      T.typedef_binding ^
      break_hint_space 2 ^
      block_hv false 0 (
      flat (Seplist.to_sep_list_first 
              T.first_variant_sep
              (tyconstr implicit n tvs)
              (sep (texspace ^ kwd "|" ^ texspace))
              constrs))

  
let rec pat p = match p.term with
  | P_wild(s) ->
      ws s ^
      T.pat_wildcard 

  | P_as(s1,p,s2,(n,l),s3) ->
      ws s1 ^ 
      pat p ^
      ws s2 ^ 
      T.pat_as ^
      Name.to_output Term_var n ^
      ws s3

  | P_typ(s1,p,s2,t,s3) ->
      ws s1 ^
      kwd "(" ^
      pat p ^
      ws s2 ^
      T.typ_sep ^
      typ t ^
      ws s3 ^
      kwd ")"
  | P_var(n) ->
      Name.to_output Term_var n
  | P_const(cd,ps) ->
      let oL = B.pattern_application_to_output pat cd ps (use_ascii_rep_for_const cd) in
      concat texspace oL
  | P_record(s1,fields,s2) ->
      ws s1 ^
      T.pat_rec_start ^
      flat (Seplist.to_sep_list patfield (sep T.rec_sep) fields) ^
      ws s2 ^
      T.pat_rec_end

  | P_tup(s1,ps,s2) ->
      ws s1 ^
      kwd "(" ^
      flat (Seplist.to_sep_list pat (sep T.tup_sep) ps) ^
      ws s2 ^
      kwd ")"

  | P_list(s1,ps,s2) ->
      ws s1 ^
      T.list_begin ^
      flat 
        (Seplist.to_sep_list_last T.last_list_sep 
           pat (sep T.list_sep) ps) ^
      ws s2 ^
      T.list_end

  | P_vector(s1,ps,s2) ->
      ws s1 ^
      T.vector_begin ^
      flat
        (Seplist.to_sep_list_last Seplist.Optional pat (sep (kwd ";")) ps) ^
      ws s2 ^
      T.vector_end

  | P_vectorC(s1,ps,s2) ->
      ws s1 ^
      kwd "[|" ^
      flat (List.map pat ps) ^
      ws s2 ^
      kwd "|]"

  | P_paren(s1,p,s2) ->
      ws s1 ^
      kwd "(" ^
      pat p ^
      ws s2 ^
      kwd ")"

  | P_cons(p1,s,p2) ->
      pat p1 ^ 
      ws s ^
      T.cons_op ^
      pat p2

  | P_num_add ((n, _),s1,s2,i) ->
      (Name.to_output Term_var n) ^
      ws s1 ^
      T.pat_add_op ^
      ws s2 ^
      T.const_num i

  | P_lit(l) ->
      lit l (annot_to_typ p)

  | P_var_annot(n,t) ->
      kwd "(" ^
      Name.to_output Term_var n ^
      T.typ_sep ^
      typ t ^
      kwd ")"

and patfield (fd,s1,p) =
  field_ident_to_output fd ^
  ws s1 ^
  kwd "=" ^
  pat p

and patlist ps = 
  match ps with
  | [] -> emp
  | [p] -> pat p
  | p::((_::_) as ps') -> pat p ^ texspace ^ patlist ps'

let backend sk i =
  ws sk ^
  (if T.target = Target_ident then meta "`" else emp) ^
  Ident.to_output Term_const T.path_sep i ^
  (if T.target = Target_ident then meta "`" else emp) 

let rec exp e = 
let is_user_exp = is_pp_exp e in
match C.exp_to_term e with
  | Var(n) ->
      Name.to_output Term_var n
  | Backend(sk, i) ->
      backend sk i
  | Nvar_e(s,n) ->
      ws s ^ id Nexpr_var (Ulib.Text.(^^^) T.nexp_var (Nvar.to_rope n))

  | Constant(cd) ->
      Output.concat emp (B.function_application_to_output (exp_to_locn e) exp false e cd [] (use_ascii_rep_for_const cd))

  | Fun(s1,ps,s2,e) ->
      ws s1 ^
      T.fun_start ^
      T.fun_kwd ^
      patlist ps ^
      ws s2 ^
      T.fun_sep ^
      exp e ^
      T.fun_end

  | Function(s1,f,s2) ->
      ws s1 ^
      T.function_start ^
      flat (Seplist.to_sep_list 
              (fun (p,s1,e,l) ->
                 pat p ^
                 ws s1 ^
                 T.fun_sep ^
                 exp e) 
              (sep (kwd "|"))
              f) ^
        ws s2 ^
      T.function_end

  | App(e1,e2) ->
      let trans e = block (is_pp_exp e) 0 (exp e) in
      let sep = (texspace ^ break_hint_space 2) in

      let oL = begin
         (* try to strip all application and see whether there is a constant at the beginning *)
         let (e0, args) = strip_app_exp e in
         match C.exp_to_term e0 with
           | Constant cd -> 
             (* constant, so use special formatting *)
             B.function_application_to_output (exp_to_locn e) trans false e cd args (use_ascii_rep_for_const cd)
           | _ -> (* no constant, so use standard one *)
             List.map trans (e0 :: args)
      end in
      let o = Output.concat sep oL in
      block is_user_exp 0 o

  | Infix(e1,e2,e3) ->      
      let trans e = block (is_pp_exp e) 0 (exp e) in
      let sep = (texspace ^ break_hint_space 2) in

      let oL = begin
         (* check, whether there is a constant in the middle *)
         match C.exp_to_term e2 with
           | Constant cd -> 
             (* constant, so use special formatting *)
             B.function_application_to_output (exp_to_locn e) trans true e cd [e1;e3] (use_ascii_rep_for_const cd)
           | _ -> (* no constant, so use standard one *)
             List.map trans [e1;e2;e3]
      end in
      let o = Output.concat sep oL in
      block is_user_exp 0 o

  | Record(s1,fields,s2) ->
      ws s1 ^
      T.rec_start ^
      flat 
        (Seplist.to_sep_list_last 
           T.last_rec_sep 
           expfield (sep T.rec_sep) fields) ^
      ws s2 ^
      T.rec_end

  | Recup(s1,e,s2,fields,s3) ->
        ws s1 ^
        T.recup_start ^
        exp e ^
        ws s2 ^
        T.recup_middle ^ 
        flat 
          (Seplist.to_sep_list_last 
             T.last_rec_sep 
             expfieldup (sep T.rec_sep) fields) ^
        ws s3 ^
        T.recup_end
  | Field(e,s,fd) ->
      if (T.target = Target_no_ident Target_isa) then
        kwd "(" ^ T.field_access_start ^ 
        field_ident_to_output fd ^
        T.field_access_end ^ 
        exp e ^ kwd ")" ^
        ws s
      else 
        exp e ^
        ws s ^
        T.field_access_start ^
        field_ident_to_output fd ^
        T.field_access_end

  | Case(b,s1,e,s2,cases,s3) ->
      block_hv is_user_exp 0 (
      ws s1 ^
      T.case_start ^
      exp e ^
      ws s2 ^
      T.case_sep1 ^
      break_hint_space 4 ^
      flat 
        (Seplist.to_sep_list_first 
           T.first_case_sep case_line 
           (sep (break_hint_space 2 ^ T.case_sep2))
           cases) ^
      ws s3 ^
      break_hint_space 0 ^
      T.case_end)

  | Typed(s1,e,s2,t,s3) ->
      ws s1 ^
      kwd "(" ^
      exp e ^
      ws s2 ^
      T.typ_sep ^
      typ t ^
      ws s3 ^
      kwd ")"

  | Let(s1,bind,s2,e) ->
      block is_user_exp 0 (
      ws s1 ^
      T.let_start ^
      block is_user_exp 0 (letbind Types.TNset.empty bind) ^
      ws s2 ^
      T.let_in ^
      break_hint_space 0 ^
      exp e ^
      T.let_end)

  | Tup(s1,es,s2) ->
      block is_user_exp 0 (  
      ws s1 ^
      kwd "(" ^
      flat (Seplist.to_sep_list exp (sep T.tup_sep) es) ^
      ws s2 ^
      kwd ")")
  | List(s1,es,s2) ->
      block is_user_exp 0 (
      ws s1 ^
      T.list_begin ^
      flat 
        (Seplist.to_sep_list_last T.last_list_sep 
           exp (sep T.list_sep) es) ^
      ws s2 ^
      T.list_end)
  | Vector(s1,es,s2) ->
      block is_user_exp 0 (
      ws s1 ^
      T.vector_begin ^
      flat
         (Seplist.to_sep_list_last T.last_list_sep
            exp (sep T.list_sep) es) ^ (* TODO KG Probably shouldn't be relying on the list sep operator here *)
      ws s2 ^
      T.vector_end)

  | VectorAcc(e,s1,n,s2) ->
      exp e ^ ws s1 ^
      kwd "." ^ kwd "[" ^ (* NOTE KG: Splitting .[ because need space in ident backend is not sophisticated enough to recognize this case *)
      nexp n ^
      ws s2 ^ kwd "]" 

  | VectorSub(e,s1,n1,s2,n2,s3) ->
      exp e ^ ws s1 ^
      kwd "." ^ kwd "[" ^ (* NOTE KG: see above *)
      nexp n1 ^ ws s2 ^ kwd ".." ^
      nexp n2 ^ ws s3 ^ kwd "]"

  | Paren(s1,e,s2) ->
      block is_user_exp 0 (ws s1 ^ kwd "(" ^ block is_user_exp 0 (exp e ^ ws s2) ^ kwd ")")

  | Begin(s1,e,s2) ->
      ws s1 ^ T.begin_kwd ^ exp e ^ ws s2 ^ T.end_kwd

  | If(s1,e1,s2,e2,s3,e3) ->
      block is_user_exp 0 (
      ws s1 ^
      break_hint_cut ^
      T.cond_if ^
      block (is_pp_exp e1) 0 (exp e1) ^
      ws s2 ^
      T.cond_then ^
      break_hint_space 2 ^
      block (is_pp_exp e2) 0 (exp e2) ^
      ws s3 ^
      break_hint_space 0 ^
      T.cond_else ^
      break_hint_space 2 ^
      block (is_pp_exp e3) 0 (exp e3))

  | Lit(l) ->
      lit l (exp_to_typ e)

  | Set(s1,es,s2) -> 
      block is_user_exp 0 (
      ws s1 ^
      (if (Seplist.is_empty es) then 
         T.const_empty s2
       else (
         T.set_start ^
         flat 
           (Seplist.to_sep_list_last 
           T.last_set_sep 
           exp (sep T.set_sep) es) ^
         ws s2 ^
         T.set_end)
      ))

  | Setcomp(s1,e1,s2,e2,s3,vars) ->
      ws s1 ^
      T.set_start ^
      exp e1 ^
      ws s2 ^
      (if T.target = Target_no_ident Target_isa then 
         (if (is_var_tup_exp e1 && NameSet.equal vars (nfmap_domain (C.exp_to_free e1))) then kwd "." else 
          T.setcomp_sep ^
          flat (List.map (fun x -> id Term_var (Name.to_rope x)) (NameSet.elements vars)) ^
          T.setcomp_binding_middle)
       else 
         T.setcomp_sep) ^
      exp e2 ^
      ws s3 ^
      T.set_end

  (* List comprehensions *)
  | Comp_binding(true,s1,e1,s2,s5,qbs,s3,e2,s4) ->
      ws s1 ^
      kwd "[" ^
      exp e1 ^
      ws s2 ^
      kwd "|" ^
      ws s5 ^
      T.setcomp_binding_start ^
      concat T.setcomp_binding_sep (List.map quant_binding qbs) ^
      ws s3 ^
      T.setcomp_binding_middle ^ 
      exp e2 ^
      ws s4 ^
      kwd "]"

  (* Set comprehensions *)
  | Comp_binding(false,s1,e1,s2,s5,qbs,s3,e2,s4) ->
      ws s1 ^
      T.set_start ^
      exp e1 ^
      ws s2 ^
      kwd "|" ^
      ws s5 ^
      T.setcomp_binding_start ^
      concat T.setcomp_binding_sep (List.map quant_binding qbs) ^
      ws s3 ^
      T.setcomp_binding_middle ^ 
      exp e2 ^
      ws s4 ^
      T.set_end

  (* TODO: Add an Isabelle transformation to nested Quants *)
  | Quant(q,qbs,s2,e) ->
      if (T.target = Target_no_ident Target_isa) then 
        block is_user_exp 0 (
        kwd "(" ^ 
        flat (List.map (isa_quant q) qbs) ^
        break_hint_space 2 ^
        block (is_pp_exp e) 0 (
        ws s2 ^ exp e) ^
        kwd ")")
      else 
        block is_user_exp 0 (
        begin
          match q with
          | Ast.Q_forall(s1) ->
              ws s1 ^ T.forall
          | Ast.Q_exists(s1) ->
              ws s1 ^ T.exists
        end ^
        flat (interspace (List.map quant_binding qbs)) ^
        ws s2 ^
        kwd "." ^
        texspace ^
        break_hint_space 2 ^
        block is_user_exp 0 (
        exp e))

  | Do(s1,m,do_lns,s2,e,s3,_) ->
      ws s1 ^
      kwd "do" ^
      Ident.to_output Module_name T.path_sep (B.module_id_to_ident m) ^
      do_lines do_lns ^
      ws s2 ^
      kwd "in" ^
      exp e ^
      ws s3 ^
      kwd "end"
          
and do_lines = function
  | [] -> emp
  | (Do_line(p,s1,e,s2)::lns) ->
      pat p ^
      ws s1 ^
      kwd "<-" ^
      exp e ^
      ws s2 ^
      kwd ";" ^
      do_lines lns

and quant_binding = function
  | Qb_var(n) -> 
      Name.to_output Term_var n.term
  | Qb_restr(is_lst,s1,p,s2,e,s3) ->
      ws s1 ^
      T.quant_binding_start ^
      pat p ^
      ws s2 ^
      (if is_lst then T.list_quant_binding else T.set_quant_binding) ^
      exp e ^
      ws s3 ^
      T.quant_binding_end

and isa_quant q qb = match q with
  | Ast.Q_forall(s1) -> 
      ws s1 ^ T.forall ^ (quant_binding qb) ^ kwd "." ^ space
  | Ast.Q_exists(s1) ->
      ws s1 ^ T.exists ^ (quant_binding qb) ^ kwd "." ^ space

and expfield (fd,s1,e,_) =
  field_ident_to_output fd ^
  ws s1 ^
  T.record_assign ^
  exp e

and expfield_coq (fd,s1,e,_) =
  ws s1 ^ kwd "(" ^
  exp e ^ kwd ")"

and expfieldup (fd,s1,e,_) =
  field_ident_to_output fd ^
  ws s1 ^
  T.recup_assign ^
  exp e

and case_line (p,s1,e,_) =
  pat p ^
  ws s1 ^
  T.case_line_sep ^
  block (is_pp_exp e) 2 (exp e)

and tyvar_binding tvs = emp
(*
  if T.target = Some (Ast.Target_coq None) then
    let tyvars = intercalate (kwd " ")
        (List.map (
          fun tv ->
            id Type_var (Ulib.Text.(^^^) T.typ_var (Tyvar.to_rope tv))
        ) (Types.TVset.elements tvs))
    in
      if List.length tyvars = 0 then
        emp
      else
        kwd "{" ^ flat tyvars ^ kwd " : Type}"
  else 
    emp
*)

and funcl_aux tvs (n, ps, topt, s1, e) =
  ws (Name.get_lskip n) ^ 
  T.funcase_start ^
  Name.to_output Term_var (Name.replace_lskip n None) ^
  tyvar_binding tvs ^
  (match ps with [] -> emp | _ -> texspace) ^
  patlist ps ^
  begin
    match topt with
      | None -> emp 
      | Some(s,t) -> ws s ^ T.typ_sep ^ typ t
  end ^
  ws s1 ^
  T.def_binding ^
  exp (if is_human_target T.target then e else mk_opt_paren_exp e) ^
  T.funcase_end

and funcl tvs (({term = n}, c, ps, topt, s1, e):funcl_aux) =
  funcl_aux tvs (B.const_ref_to_name n false c, ps, topt, s1, e)    

and letbind tvs (lb, _) : Output.t = match lb with
  | Let_val(p,topt,s2,e) ->
      pat p ^
      tyvar_binding tvs ^ 
      begin
        match topt with
          | None -> emp 
          | Some(s,t) -> ws s ^ T.typ_sep ^ typ t
      end ^
      ws s2 ^ T.def_binding ^ exp (if is_human_target T.target then e else mk_opt_paren_exp e)
  | Let_fun (n, ps, topt, s1, e) ->
      funcl_aux tvs (n.term, ps, topt, s1, e)


(* In Isabelle we have to handle the following three cases for type definitions
 * separately: 
 * - record types have to be defined usind the record keyword
 * - simple type aliases like type time = num are handled using the types
 *   keyword
 * - Types with constuctors like type t = a | b are introduced using the
 *   datatype keyword
let tdef_start = function 
  | Te_opaque ->
      T.typedef_start
  | Te_abbrev(_,_) ->
      T.type_abbrev_start 
  | Te_record(_,_,_,_) ->
      T.typedefrec_start 
  | Te_record_coq(_,_,_,_,_) ->
      T.typedefrec_start 
  | Te_variant(_,_) ->
      T.typedef_start  
  | Te_variant_coq(_,_) ->
      T.typedef_start  
 *)   

let tdef_tvars ml_style tvs = 
  let tdef_tnvar tv =
    match tv with
      | Tn_A _ -> tyvar tv
      | Tn_N _ -> if (T.nexp_params_vis) 
                     then tyvar tv
                     else T.nexp_start ^ tyvar tv ^ T.nexp_end
  in
  match tvs with
    | [] -> emp
    | [tv] ->
        T.before_tyvars ^
        tdef_tnvar tv ^
        T.after_tyvars
    | tvs ->
        let s = if ml_style then T.tup_sep else emp in
          T.before_tyvars ^
          (if (T.nexp_params_vis) then 
             ((if ml_style then kwd "(" else emp) ^
              (flat (Seplist.to_sep_list tyvar (sep s) (Seplist.from_list (List.map (fun tv -> (tv,None)) tvs)))) ^
              (if ml_style then kwd ")" else emp))
          else (bracket_omit tyvar (fun t f s -> match t with | Tn_A _ -> f t ^ s | Tn_N _ -> T.nexp_start ^ (f t) ^ T.nexp_end) (fun f t -> (t,None)) s
                                   (if ml_style then kwd "(" else emp) (if ml_style then kwd ")" else emp) tvs))
          ^
          T.after_tyvars

let tdef_tctor quoted_name tvs n regexp =
  let nout = 
    if quoted_name then Name.to_output_quoted "\"" "\"" Type_ctor n else Name.to_output Type_ctor n 
  in
  let regexp_out = 
    match regexp with | None -> emp
                      | Some(Name_restrict(sk1,(x,l),sk2,sk3,s,sk4)) -> 
                              ws sk1 ^ T.name_start ^ Name.to_output Term_var x ^ ws sk2 ^ kwd "=" ^ ws sk3 ^ str (Ulib.Text.of_latin1 s) ^ T.name_end ^ ws sk4 
  in 
    if T.type_params_pre then
      tdef_tvars true tvs ^ regexp_out ^
      nout 
    else
      (* FZ slightly distasteful: in this case we know that the backend *)
      (* is Coq and we do not print parentheses; however parentheses *)
      (* should be parametrised *)
      nout ^
      tdef_tvars false tvs ^ regexp_out

let tdef ((n0,l), tvs, t_path, texp, regexp) =
  let n = B.type_path_to_name n0 t_path in 
  let n' = Name.to_output Type_ctor n in
  let tvs' = List.map (fun tn -> (match tn with | Tn_A (x, y, z) -> kwd (Ulib.Text.to_string y)
                                                | Tn_N (x, y, z) -> kwd (Ulib.Text.to_string y))) tvs in
    tdef_tctor false tvs n regexp ^ tyexp true n' tvs' texp 

let range = function
  | GtEq(_,n1,s,n2) -> nexp n1 ^ ws s ^ kwd ">=" ^ nexp n2
  | Eq(_,n1,s,n2) -> nexp n1 ^ ws s ^ kwd "=" ^ nexp n2

let constraints = function
  | None -> emp
  | Some(Cs_list(l_c,op_s,l_r,s)) ->
      flat (Seplist.to_sep_list
              (fun (id,tv) ->
                 Ident.to_output Type_var T.path_sep id ^
                 tyvar tv)
              (sep (kwd","))
              l_c) ^
      (match op_s with
        | None -> emp
        | Some s1 -> ws s1 ^ kwd ";") ^
      flat (Seplist.to_sep_list range (sep (kwd",")) l_r) ^
      ws s ^
      kwd "=>"

let constraint_prefix (Cp_forall(s1,tvs,s2,constrs)) =
  ws s1 ^
  T.forall ^
  flat (List.map tyvar tvs) ^
  ws s2 ^
  kwd "." ^
  constraints constrs

let indreln_name (RName(s1,name,name_ref,s2,(constraint_pre,t),witness,checks,functions,s3)) =
  ws s1 ^
  T.reln_name_start ^ 
  (Name.to_output Term_method (B.const_ref_to_name name false name_ref)) ^ ws s2 ^
  T.typ_sep ^
      begin
        match constraint_pre with
          | None -> emp
          | Some(cp) -> constraint_prefix cp
      end ^
      typ t ^  
  ws s3 ^
  T.reln_name_end

let indreln_clause (Rule(name, s0, s1, qnames, s2, e_opt, s3, rname, rname_ref, es),_) =
  (if T.reln_clause_show_name then (
    ((if T.reln_clause_quote_name then Name.to_output_quoted "\"" "\"" else Name.to_output) Term_method name ^
      ws s0 ^
      kwd ":"
    )
  ) else emp) ^
  ws s1 ^ T.reln_clause_start ^
  (*Indreln TODO does not print format annotated variables with their types find*)
  (if (T.reln_clause_show_empty_quant || List.length qnames > 0) then (
    T.reln_clause_quant ^
    flat (interspace (List.map (fun (QName n) -> Name.to_output Term_var n.term) qnames)) ^
    ws s2 ^ 
    kwd "."
  ) else emp) ^
  (match e_opt with None -> ws s3 | Some e -> 
     exp (if T.reln_clause_add_paren then Typed_ast_syntax.mk_opt_paren_exp e else e) ^ 
     ws s3 ^ kwd "==>") ^
  Name.to_output Term_var (B.const_ref_to_name rname.term false rname_ref) ^
  flat (interspace (List.map exp es)) ^
  T.reln_clause_end

let targets_opt = function
  | None -> emp
  | Some((b,s1,targets,s2)) ->
      ws s1 ^
      (if b then kwd "~{" else kwd "{") ^
      flat (Seplist.to_sep_list target_to_output (sep T.set_sep) targets) ^
      ws s2 ^
      kwd "}"

let in_target targs = Typed_ast.in_targets_opt T.target targs


(****** Isabelle ******)

let isa_op_typ texp = match texp.term with
  | Typ_fn(_,_,_) -> kwd "[" ^ typ texp ^ kwd "]"
  | _ -> typ texp


(* let quote_ident name = match (name : Output.t) with 
*)

(* isa_mk_typed_def_header:
 * generates the Isar 'name-type' line of the form 
 *      name :: "type" where \n
 * for each top-level definition name, we check whether it is a isa(r) keyword
 * and in case it is, we put the name in double quotes.
 * isa-keywords is defined in isa_keyowrds.ml
*)

let isa_mk_typed_def_header (name, ptyps, s, etyp) : Output.t = 
  name ^ kwd " " ^ T.typ_sep ^ kwd " \"" ^ 
  flat (List.map (function x -> isa_op_typ (C.t_to_src_t x) ^ T.typ_fun_sep) ptyps) ^
  typ (C.t_to_src_t etyp) ^ 
  kwd "\" " ^ ws s 

(*
  flat (List.map (function x -> (isa_op_typ (C.t_to_src_t x.typ) ^ 
  if es=[] then emp else T.typ_fun_sep)) ps) ^
  flat (List.map (function ex -> typ (C.t_to_src_t (exp_to_typ ex))) es) ^ 
*)

let isa_is_simple_funcl_aux ((_, _, ps, _, _, _):funcl_aux) : bool = 
   List.for_all (fun p -> (Pattern_syntax.is_var_wild_pat p)) ps

let isa_funcl_header (({term = n}, c, ps, topt, s1, (e : Typed_ast.exp)):funcl_aux) =
  isa_mk_typed_def_header (Name.to_output Term_var (B.const_ref_to_name n false c), List.map Typed_ast.annot_to_typ ps, s1, exp_to_typ e)

let isa_funcl_header_seplist clause_sl =
  let clauseL = Seplist.to_list clause_sl in
  let (_, clauseL_filter) = List.fold_left (fun (ns, acc) (({term = n'}, n'_ref, _, _, _, _) as c) ->
     let n = Name.strip_lskip (B.const_ref_to_name n' false n'_ref) in if NameSet.mem n ns then (ns, acc) else (NameSet.add n ns, c :: acc)) (NameSet.empty, []) clauseL in

  let headerL = List.map isa_funcl_header clauseL_filter in
  (Output.concat (kwd "\n                   and") headerL) ^ (kwd "where \n    ")


let isa_funcl_header_indrel_seplist clause_sl =
  let clauseL = Seplist.to_list clause_sl in
  let (_, clauseL_filter) = List.fold_left (fun (ns, acc) (Rule(_,_, _, _, _, _, _, rname, c, _),_) ->
      let n = Name.strip_lskip rname.term in 
      if NameSet.mem n ns then (ns, acc) else (NameSet.add n ns, rname :: acc)) (NameSet.empty, []) clauseL in
  let headerL = List.map (fun rname -> 
        isa_mk_typed_def_header(Name.to_output Term_var rname.term,[], None,
                Typed_ast.annot_to_typ rname)) clauseL_filter in
  (Output.concat (kwd "\n      and") headerL) ^ (kwd "where")        


let isa_funcl_default eqsign (({term = n}, c, ps, topt, s1, (e : Typed_ast.exp)):funcl_aux) =
  kwd "\"" ^ Name.to_output Term_var (B.const_ref_to_name n false c) ^ flat (List.map pat ps)^ ws s1 ^ eqsign ^ kwd "(" ^ exp e ^ kwd ")\""

let isa_funcl_abs eqsign (({term = n}, c, ps, topt, s1, (e : Typed_ast.exp)):funcl_aux) =
  kwd "\"" ^ Name.to_output Term_var (B.const_ref_to_name n false c) ^ ws s1 ^ eqsign ^ kwd "(%" ^ flat (List.map pat ps) ^ kwd ". " ^ exp e ^ kwd ")\""

let isa_funcl simple =
(*  if simple then isa_funcl_abs (kwd "= ") else isa_funcl_default (kwd "= ") *)
  isa_funcl_default (kwd "= ")

let isa_funcl_aux simple (clause:funcl_aux) : Output.t = 
      isa_funcl_header clause ^ kwd "where \n" ^ isa_funcl simple clause

(******* End Isabelle ********)

let rec hol_strip_args_n type_names n ts =
  match type_names with
    | [] -> false
    | (n',tvs)::type_names -> 
        if n = n' then 
          (* TODO: check that ts and tvs correspond.  Otherwise, this type
           * definition isn't expressible in HOL, and dropping the arguments
           * makes a different type *)
          true 
        else 
          hol_strip_args_n type_names n ts

let rec hol_strip_args_t type_names t = match t.term with
  | Typ_wild(sk) -> t
  | Typ_var(sk,tv) -> t
  | Typ_len(n) -> t
  | Typ_fn(t1,sk,t2) -> 
      { t with term = Typ_fn(hol_strip_args_t type_names t1, sk, hol_strip_args_t type_names t2) }
  | Typ_tup(ts) -> 
      { t with term = Typ_tup(Seplist.map (hol_strip_args_t type_names) ts) }
  | Typ_app(id,ts) ->
      begin
        match id.id_path with
          | Id_none sk -> 
              { t with term = Typ_app(id, List.map (hol_strip_args_t type_names) ts) }
          | Id_some p ->
              match Ident.to_name_list p with
                | ([],n) ->
                    if hol_strip_args_n type_names n ts then
                      { t with term = Typ_app(id,[]) }
                    else
                      { t with term = Typ_app(id, List.map (hol_strip_args_t type_names) ts) }
                | _ -> 
                    { t with term = Typ_app(id, List.map (hol_strip_args_t type_names) ts) }
      end
  | Typ_backend(id,ts) ->
      begin
        match id.id_path with
          | Id_none sk -> 
              { t with term = Typ_backend(id, List.map (hol_strip_args_t type_names) ts) }
          | Id_some p ->
              match Ident.to_name_list p with
                | ([],n) ->
                    if hol_strip_args_n type_names n ts then
                      { t with term = Typ_backend(id,[]) }
                    else
                      { t with term = Typ_backend(id, List.map (hol_strip_args_t type_names) ts) }
                | _ -> 
                    { t with term = Typ_backend(id, List.map (hol_strip_args_t type_names) ts) }
      end
  | Typ_paren(sk1,t,sk2) -> 
      { t with term = Typ_paren(sk1,hol_strip_args_t type_names t, sk2) }

let hol_strip_args_ctors type_names (n_l,c_ref,sk,ts) =
  (n_l,c_ref, sk, Seplist.map (hol_strip_args_t type_names) ts)

let hol_strip_args_texp type_names texp = match texp with
  | Te_opaque -> Te_opaque
  | Te_abbrev(sk,t) -> Te_abbrev(sk,t)
  | Te_record(sk1,sk2,stuff,sk3) -> Te_record(sk1,sk2,stuff,sk3)
  | Te_variant(sk1, ctors) ->
      Te_variant(sk1, Seplist.map (hol_strip_args_ctors type_names) ctors)

let hol_strip_args type_names ((n,l), tvs, type_path, texp,optreg) =
  ((n,l),
   [],
   type_path,
   hol_strip_args_texp type_names texp,
   optreg)

let collect_type_names defs = 
  Seplist.to_list_map 
    (fun ((n,l),tvs,type_path,_,_) -> (Name.strip_lskip n, tvs))
    defs

let is_abbrev l = 
  Seplist.length l = 1 &&
  match Seplist.hd l with
    | (_,_,_,Te_abbrev _,_) -> true
    | _ -> false

let is_rec l = 
  Seplist.length l = 1 &&
  match Seplist.hd l with
    | (_,_,_,Te_record _,_) -> true
    | _ -> false

let rec isa_def_extra (gf:extra_gen_flags) d l : Output.t = match d with
  | Val_def(Fun_def(s1, s2_opt, targets, clauses),tnvs, class_constraints) 
      when gf.extra_gen_termination -> 
      let (_, is_rec) = Typed_ast_syntax.is_recursive_def d in
      if (in_target targets && is_rec) then
      begin
        let n = 
          match Seplist.to_list clauses with
            | [] -> assert false
            | (n, c, _, _, _, _)::_ -> Name.strip_lskip (B.const_ref_to_name n.term false c)
        in
          kwd "termination" ^ space ^ 
          kwd (Name.to_string n) ^ space ^
          kwd "by" ^ space ^ kwd "lexicographic_order" ^
          new_line ^ new_line 
      end
      else emp
  | Lemma (_, lty, targets, n_opt, sk1, e, sk2) when (extra_gen_flags_gen_lty gf lty && in_target targets) -> begin
      let lem_st = match lty with
                     | Ast.Lemma_theorem _ -> "theorem"
                     | _ -> "lemma" in
      let solve = match lty with
                     | Ast.Lemma_assert _ -> "by eval"
                     | _ -> "(* try *) by auto" in
      (kwd lem_st ^ space ^
      (match n_opt with None -> emp | Some ((n, _), sk1) -> kwd (Name.to_string (Name.strip_lskip n)) ^ ws sk1 ^ kwd ":") ^
      new_line ^
      kwd "\"" ^
      exp e ^
      ws sk2 ^
      kwd "\"" ^
      new_line ^
      kwd solve ^
      new_line ^
      new_line)
    end
  | _ -> emp

let rec hol_def_extra gf d l : Output.t = match d with
  | Val_def(Fun_def(s1, s2_opt, targets, clauses),tnvs, class_constraints) 
      when gf.extra_gen_termination -> 
      let (_, is_rec) = Typed_ast_syntax.is_recursive_def d in
      if (in_target targets && is_rec) then
      begin
        let n = 
          match Seplist.to_list clauses with
            | [] -> assert false
            | (n, c, _, _, _, _)::_ -> Name.to_string (Name.strip_lskip (B.const_ref_to_name n.term false c))
        in
        let goal_stack_setup_s = Format.sprintf "(* val gst = Defn.tgoal_no_defn (%s_def, %s_ind) *)\n" n n in
        let proof_s = Format.sprintf "val (%s_rw, %s_ind_rw) =\n  Defn.tprove_no_defn ((%s_def, %s_ind),\n    (* the termination proof *)\n  )\n" n n n n in
        let store_s = Format.sprintf "val %s_rw = save_thm (\"%s_rw\", %s_rw);\nval %s_ind_rw = save_thm (\"%s_ind_rw\", %s_ind_rw);\n" n n n n n n in
        meta (String.concat "" [goal_stack_setup_s; proof_s; store_s; "\n\n"])
      end
      else emp
  | Lemma (sk0, lty, targets, n_opt, sk1, e, sk2) when (extra_gen_flags_gen_lty gf lty && in_target targets) -> begin
      let start = match n_opt with 
          None -> "val _ = prove(\n" | 
          Some ((n, _), _) -> begin
            let n_s = (Name.to_string (Name.strip_lskip n)) in
            match lty with
                     | Ast.Lemma_assert _ -> Format.sprintf "val %s = prove(\n" n_s
                     | _ -> Format.sprintf "val %s = store_thm(\"%s\",\n" n_s n_s 
          end
      in
      let tactic_s = match lty with
                     | Ast.Lemma_assert _ -> "  EVAL_TAC"
                     | _ -> "  (* your proof *)"
      in
      let (e', _) = alter_init_lskips (fun _ -> (None, None)) e in
      kwd start ^
      kwd "``" ^
      exp e' ^
      kwd "``," ^
      new_line ^
      meta tactic_s ^
      new_line ^
      kwd ");" ^
      new_line ^
      new_line
    end
  | _ -> emp

let rec ocaml_def_extra gf d l : Output.t = match d with
  | Lemma (sk0, lty, targets, n_opt, sk1, e, sk2) when (extra_gen_flags_gen_lty gf lty && in_target targets) -> begin
      let is_assert = match lty with
                     | Ast.Lemma_assert _ -> true
                     | _ -> false in
      if not (is_assert) then emp else 
      begin
        let n_s = match n_opt with 
          | None -> "\"-\"" 
          | Some ((n, _), _) -> 
              Format.sprintf "\"%s\"" (String.escaped (Name.to_string (Name.strip_lskip n)))
        in
        let loc_s = Format.sprintf "\"%s\\n\"" (String.escaped (Reporting_basic.loc_to_string true l)) in 
        let (e', _) = alter_init_lskips (fun _ -> (None, None)) e in
        meta (Format.sprintf "let _ = run_test %s %s (\n  " n_s loc_s) ^
        exp e' ^
        meta "\n)\n\n"
      end
    end
  | _ -> emp


let infix_decl = function
  | Ast.Fixity_default_assoc -> emp
  | Ast.Fixity_non_assoc (sk, n) -> ws sk ^ kwd "non_assoc" ^ num n
  | Ast.Fixity_left_assoc (sk, n) -> ws sk ^ kwd "left_assoc" ^ num n
  | Ast.Fixity_right_assoc (sk, n) -> ws sk ^ kwd "right_assoc" ^ num n


let rec def_internal callback (inside_module : bool) d is_user_def : Output.t = match d with
  (* A single type abbreviation *)
  | Type_def(s1, l) when is_abbrev l->
      begin
        match Seplist.hd l with
          | ((n,l),tvs,t_p,Te_abbrev(s4,t),regexp) ->
              ws s1 ^
              block is_user_def 0 (
              T.type_abbrev_start ^
              tdef_tctor T.type_abbrev_name_quoted tvs (B.type_path_to_name n t_p) regexp ^
              tyexp_abbrev s4 t ^
              T.type_abbrev_end)
          | _ -> assert false
      end

  (* A single record definition *)
  | Type_def(s1, l) when is_rec l->
      begin
        match Seplist.hd l with
          | ((n,l'),tvs, t_p, Te_record(s4,s5,fields,s6),regexp) ->
              ws s1 ^
              block is_user_def 0 (
              T.typedefrec_start ^		
              tdef_tctor false tvs (B.type_path_to_name n t_p) regexp ^
              tyexp_rec s4 s5 fields s6 ^
              T.typedefrec_end) (*
              if T.target = Some (Ast.Target_coq None) then
                kwd "\n" ^
                let l = Seplist.to_list l in
                let m = List.map (fun (name, vars, exp) ->
                  let (lskips_t, l) = name in
                  let o = kwd (Ulib.Text.to_string (Name.to_rope (Name.strip_lskip lskips_t))) in
                    generate_coq_boolean_equality tvs o exp
                  ) l
                in
                let i = intercalate (kwd "\n") m in
                let f = List.fold_right (^) i (kwd "") in
                  f ^ kwd "\n" ^
                  generate_coq_record_update_notation r
              else
                emp *)
          | _ -> assert false
      end
  | Type_def(s, defs) ->
      let defs = 
        if T.target = Target_no_ident Target_hol then 
          Seplist.map (hol_strip_args (collect_type_names defs)) defs 
        else 
          defs 
      in
        ws s ^
        block is_user_def 2 (
        T.typedef_start ^
        flat (Seplist.to_sep_list tdef (sep (break_hint_space 0 ^ T.typedef_sep)) defs) ^
        T.typedef_end) (*
        if T.target = Some (Ast.Target_coq None) then
          kwd "\n" ^ (* generate_coq_decidable_equalities defs *)
          let l = Seplist.to_list defs in
          let m = List.map (fun (name, vars, exp) ->
            let (lskips_t, l) = name in
            let o = kwd (Ulib.Text.to_string (Name.to_rope (Name.strip_lskip lskips_t))) in
            generate_coq_boolean_equality vars o exp
            ) l
          in
          let i = intercalate (kwd "\n") m in
          let f = List.fold_right (^) i (kwd "") in
            f
        else
          emp *)

  | Val_def(Let_def(s1, targets,(p, name_map, topt, sk, e)),tnvs,class_constraints) -> 
      (* TODO: use name_map to do proper renaming *)
      if in_target targets then
        ws s1 ^
        T.def_start ^
        (if T.target = Target_ident then
           targets_opt targets 
         else
           emp) ^
        letbind tnvs (Let_val (p, topt, sk, e), Ast.Unknown) ^
        break_hint_space 0 ^
        T.def_end
      else
        emp
  | Val_def(Fun_def(s1, rec_flag, targets, clauses),tnvs, class_constraints) -> 
      if in_target targets then
        let (is_rec, is_real_rec) = Typed_ast_syntax.is_recursive_def d in
        let s2 = match rec_flag with FR_non_rec -> None | FR_rec sk -> sk in
        let n = 
          match Seplist.to_list clauses with
            | [] -> assert false
            | (n,n_ref, _, _, _, _)::_ -> Name.strip_lskip (B.const_ref_to_name n.term false n_ref)
        in
          T.rec_def_header is_rec is_real_rec s1 s2 n ^
          (if T.target = Target_ident then
             targets_opt targets 
           else
             emp) ^
          flat (Seplist.to_sep_list (funcl tnvs) (sep T.def_sep) clauses) ^
          T.def_end ^
          T.rec_def_footer is_rec is_real_rec n
          else
        emp
  | Val_def(Let_inline(s1,s2,targets,n,c,args,s4,body),tnvs,class_constraints) ->
      if (T.target = Target_ident) then
        ws s1 ^
        kwd "let" ^
        ws s2 ^
        kwd "inline" ^
        targets_opt targets ^
        Name.to_output Term_var n.term ^
        flat (List.map (fun n -> Name.to_output Term_var n.term) args) ^ 
        ws s4 ^
        kwd "=" ^
        exp body
      else
        emp
  | Lemma (sk0, lty, targets, n_opt, sk1, e, sk2) -> 
      if (not (is_human_target T.target)) then emp else
      begin
      let lem_st = match lty with
                     | Ast.Lemma_theorem sk -> "theorem"
                     | Ast.Lemma_assert sk -> "assert"
                     | Ast.Lemma_lemma sk -> "lemma" in
      (ws sk0 ^ kwd lem_st ^ 
       targets_opt targets ^
      (match n_opt with None -> emp | Some ((n, l), sk1) -> 
       Name.to_output Term_var n ^
       ws sk1 ^ kwd ":") ^
      ws sk1 ^ kwd "(" ^ exp e ^ ws sk2 ^ kwd ")")
    end
  | Module(s1,(n,l),mod_bind,s2,s3,ds,s4) -> 
      ws s1 ^
      T.module_module ^
      Name.to_output Module_name n ^
      ws s2 ^
      kwd "=" ^
      ws s3 ^
      T.module_struct ^
      callback ds ^
      ws s4 ^
      T.module_end
  | Rename(s1,(n,l),mod_bind,s2,m) ->
      ws s1 ^
      T.module_module ^
      Name.to_output Module_name n ^
      ws s2 ^
      kwd "=" ^
      Ident.to_output Module_name T.path_sep (B.module_id_to_ident m)
  | OpenImport(Ast.OI_open s,ms) ->
      ws s ^
      T.module_open ^
      (Output.flat (List.map (fun m -> Ident.to_output Module_name T.path_sep (B.module_id_to_ident m)) ms))
  | OpenImport(Ast.OI_open_import (s1, s2),ms) ->
      if (is_human_target T.target) then
        ws s1 ^
        T.module_open ^
        ws s2 ^
        T.module_import ^
        (Output.flat (List.map (fun m -> Ident.to_output Module_name T.path_sep (B.module_id_to_ident m)) ms))
      else def_internal callback inside_module (OpenImport (Ast.OI_open (Ast.combine_lex_skips s1 s2), ms)) is_user_def
  | OpenImport(Ast.OI_import s,ms) -> 
      if (is_human_target T.target) then
        ws s ^
        T.module_import ^
        (Output.flat (List.map (fun m -> Ident.to_output Module_name T.path_sep (B.module_id_to_ident m)) ms))
      else emp
  | Indreln(s,targets,names,clauses) ->
      if in_target targets then
        ws s ^
        T.reln_start ^
        (if T.target = Target_ident then
           targets_opt targets 
         else
           emp) ^
        flat (Seplist.to_sep_list indreln_name (sep T.reln_sep) names) ^
        flat (Seplist.to_sep_list indreln_clause (sep T.reln_sep) clauses) ^
        T.reln_end
      else
        emp
  | Val_spec(s1,(n,l),n_ref,s2,(constraint_pre,t)) ->
      ws s1 ^
      T.val_start ^
      Name.to_output Term_var n ^
      ws s2 ^
      T.typ_sep ^
      begin
        match constraint_pre with
          | None -> emp
          | Some(cp) -> constraint_prefix cp
      end ^
      typ t
  | Instance(s1,(cp,s2,id,class_path,t,s3),methods,s4) ->
      ws s1 ^
      kwd "instance" ^
      begin
        match cp with
          | None -> emp
          | Some(cp) -> constraint_prefix cp
      end ^
      ws s2 ^
      kwd "(" ^
      Ident.to_output Term_method T.path_sep id ^
      typ t ^
      ws s3 ^
      kwd ")" ^
      flat (List.map (fun d -> def callback true (Val_def(d,Types.TNset.empty,[])) is_user_def) methods) ^
      ws s4 ^
      kwd "end"
  | Class(s1,s2,(n,l), tv, class_path, s3, specs, s4) -> 
      ws s1 ^
      kwd "class" ^
      ws s2 ^
      kwd "(" ^
      Name.to_output Class_name n ^
      tyvar tv ^
      ws s3 ^
      kwd ")" ^
      flat (List.map 
              (fun (s1,(n,l),f_ref,s2,t) ->
                ws s1 ^
                T.val_start ^
                Name.to_output Term_method n ^
                ws s2 ^
                kwd ":" ^
                typ t)
              specs) ^
      ws s4 ^
      kwd "end"
  | Declaration (Decl_target_rep_decl_term (sk1, targ, sk2, comp, id, args, sk3, rhs)) ->
      if (not (Target.is_human_target T.target)) then emp else begin
        ws sk1 ^
        kwd "declare" ^
        (Target.target_to_output targ) ^
        ws sk2 ^
        kwd "target_rep" ^
        component_to_output comp ^
        (Ident.to_output Term_const T.path_sep (B.const_id_to_ident id true)) ^
        (Output.concat emp (List.map (fun n -> Name.to_output Term_var n.term) args)) ^
        ws sk3 ^
        kwd "=" ^
        (match rhs with
          | Target_rep_rhs_term_replacement e -> exp e
          | Target_rep_rhs_infix (sk1, decl, sk2, i) -> begin
               ws sk1 ^
               kwd "infix" ^
               infix_decl decl ^
               backend sk2 i
            end
          | _ -> raise (Reporting_basic.err_todo true Ast.Unknown "declaration")
        ) 
      end
  | Declaration (Decl_target_rep_decl_type (sk1, targ, sk2, sk3, id, args, sk4, rhs)) ->
      if (not (Target.is_human_target T.target)) then emp else begin
        ws sk1 ^
        kwd "declare" ^
        (Target.target_to_output targ) ^
        ws sk2 ^
        kwd "target_rep" ^
        ws sk3 ^
        kwd "type" ^
        (Ident.to_output Type_ctor T.path_sep (B.type_id_to_ident id)) ^
        tdef_tvars true args ^
        ws sk4 ^
        kwd "=" ^
        typ rhs
      end
  | Declaration (Decl_compile_message_decl _) -> raise (Reporting_basic.err_todo true Ast.Unknown "compile message declaration") 
  | Comment(d) ->
      let (d',sk) = def_alter_init_lskips (fun sk -> (None, sk)) d in
        ws sk ^ ws (Some([Ast.Com(Ast.Comment([Ast.Chars(X.comment_def d')]))]))


(* for -inc.tex definitions *)


(*  latex scheme: for a top level function definition of set_option_map, we'll generate:

\newcommand{\setToptionTmap}{             latex command name
\lemdefn
{lab:setToptionTmap}                #1 latex label
{set\_option\_map}                  #2 typeset name (eg to go in index and contents line) 
{A set option map}                  #3 immediately-preceding comment
{\lemfoo{let} \ }                   #4 the left-hand-side keyword (let, type, module,...) 
{\lemfoo{set\_option\_map} \;\tsunknown{f} \;\tsunknown{xs} = {}\\{}}    #5 left hand side
{\{ (\Mcase  \;\tsunknown{f} \;\tsunknown{x} \;\Mof ...  }               #6 rhs 
{That was a set option map}         #7 immediately-following comment
}

The immediately-preceding comment is a preceding (** *) comment (if
  any) that is not separated by more than a single newline and
  spaces/tabs from this definition.
The immediately-following comment is similar. 
The typeset name should already have any tex hom applied.
The left hand side keyword, and the left hand side, should include any
  following newlines (and comments before them?) so that the rhs is
  clean.  
The concatentation of the lhs keyword, the lhs, and the rhs should be exactly what we
  print in whole-document mode (minus the "\lemdef" there).  Modulo the pre/post comments...
*)

and (^^^^) = Ulib.Text.(^^^)

and make_lemdefn latex_name latex_label typeset_name pre_comment lhs_keyword lhs rhs post_comment = 
  (r"\\newcommand{" ^^^^ latex_name ^^^^ r"}{%\n" ^^^^
  r"\\lemdefn\n" ^^^^ 
  r"{" ^^^^ latex_label ^^^^ r"}\n" ^^^^
  r"{" ^^^^ typeset_name ^^^^ r"}\n" ^^^^ 
  r"{" ^^^^ pre_comment ^^^^ r"}\n" ^^^^
  r"{" ^^^^ lhs_keyword ^^^^ r"}\n" ^^^^ 
  r"{" ^^^^ lhs ^^^^ r"}\n" ^^^^ 
  r"{" ^^^^ rhs ^^^^ r"}\n" ^^^^
  r"{" ^^^^ post_comment ^^^^ r"}%\n" ^^^^
  r"}\n",
  latex_name ^^^^ r"\n")
 


(* keep locations for latex-name-clash error reporting... *)
and names_of_pat p : (Ulib.Text.t * Ulib.Text.t * Ast.l) list = match p.term with
  | P_wild(s) ->
      []
  | P_as(s1,p,s2,(n,l),s3) ->
      let n' = Name.strip_lskip n in 
      names_of_pat p  @ [(Name.to_rope n',Name.to_rope_tex Term_var n', p.locn)]
  | P_typ(s1,p,s2,t,s3) ->
      names_of_pat p
  | P_var(n) | P_var_annot(n,_) ->
      let n' = Name.strip_lskip n in 
      [(Name.to_rope n', Name.to_rope_tex Term_var n', p.locn)]
  | P_const(cd,ps) ->
      let n = Ident.get_name (B.const_id_to_ident cd (*XXX: change*) true) in
      let n' = Name.strip_lskip n in 
      [(Name.to_rope n', Name.to_rope_tex Term_ctor n', p.locn)]
  | P_record(s1,fields,s2) ->
      List.flatten (List.map (function (_,_,p) -> names_of_pat p) (Seplist.to_list fields))
  | P_tup(s1,ps,s2) ->
      List.flatten (List.map names_of_pat (Seplist.to_list ps))
  | P_list(s1,ps,s2) ->
      List.flatten (List.map names_of_pat (Seplist.to_list ps))
  | P_vector(s1,ps,s2) ->
      List.flatten (List.map names_of_pat (Seplist.to_list ps))
  | P_vectorC(s1,ps,s2) ->
      List.flatten (List.map names_of_pat ps)
  | P_paren(s1,p,s2) ->
      names_of_pat p
  | P_cons(p1,s,p2) ->
      names_of_pat p1 @ names_of_pat p2
  | P_num_add((n,_),_,_,_) ->
      let n' = Name.strip_lskip n in 
      [(Name.to_rope n', Name.to_rope_tex Term_var n', p.locn)]
  | P_lit(l) ->
      []


and tex_of_output out = to_rope_tex out

and tex_inc_letbind (p, name_map, topt, sk, e) lhs_keyword = 
      let (source_name, typeset_name) = 
        match names_of_pat p with 
        | [(source_name, typeset_name, l)] -> (source_name, typeset_name) 
(* ghastly temporary hacks *)
        | (source_name, typeset_name, l)::_ -> (source_name, typeset_name) 
        | [] -> (gensym_tex_command(),r"")
        (* SO: The next case causes an unused case warning *)
        (*| _ -> raise (Failure "tex_inc_letbind found <> 1 name")*) in
      let latex_name = Output.tex_command_name source_name in
      let latex_label = Output.tex_command_label source_name in
      let pre_comment = r"" (* PLACEHOLDER *) in      
      let post_comment = r"" (* PLACEHOLDER *) in      
      let lhs_output = 
        begin
          pat p ^ 
          match topt with
          | None -> emp 
          | Some(s,t) -> ws s ^ T.typ_sep ^ typ t
        end ^
        ws sk ^ T.def_binding in
      let rhs_output = exp e in

      let lhs = tex_of_output lhs_output in
      let rhs = tex_of_output rhs_output in
      make_lemdefn latex_name latex_label typeset_name pre_comment lhs_keyword lhs rhs post_comment


and def_tex_inc d : (Ulib.Text.t*Ulib.Text.t) list = match d with
  | Val_def(Let_def(s1, targets,bind),tnvs,class_constraints) ->
      if in_target targets then
        let lhs_keyword = tex_of_output (ws s1 ^ T.def_start) in
        [tex_inc_letbind bind lhs_keyword]
      else
        []
  | _ -> []


and html_source_name_letbind (p, _, _, _, _) = 
    match names_of_pat p with 
      | [(source_name, typeset_name, l)] -> Some source_name
      | (source_name, typeset_name, l)::_ -> Some source_name
      | [] -> None

and html_source_name_def (d : def_aux) = match d with
  | Val_def(Let_def(s1, targets,bind),tnvs,class_constraints) ->
      html_source_name_letbind bind
  | _ -> None

and html_link_def d = 
  match html_source_name_def d with
  | None -> emp
  | Some s -> 
      let sr = Ulib.Text.to_string s in
      kwd ( String.concat "" ["\n<a name=\"";sr;"\">"])
 
(* Sets in Isabelle: the standard set notation only supports {x. P x} to define
 * a set, but for example not {f x. P x}. 
 * We use the Isabelle notation { f x | x. P x } to cope with that restriction.
 * So the general case {exp1|exp2} has to be translated to {exp1|Vars(exp1).exp2} *)
(* TODO: try to move as much as possible to trans.ml and use normal def function *)

and isa_def callback inside_module d is_user_def : Output.t = match d with 
  | Type_def(s1, l) when is_abbrev l->
      begin
        match Seplist.hd l with
          | ((n,l),tvs,t_path,Te_abbrev(s4,t),regex) ->
              ws s1 ^
              T.type_abbrev_start ^
              tdef_tctor false tvs (B.type_path_to_name n t_path) regex ^
              tyexp_abbrev s4 t ^
              T.type_abbrev_end
          | _ -> assert false
      end
  
  | Type_def(s1, l) when is_rec l->
      begin
        match Seplist.hd l with
          | ((n,l),tvs,t_path,Te_record(s4,s5,fields,s6),regex) ->
              ws s1 ^
              T.typedefrec_start ^ 
              tdef_tctor false tvs (B.type_path_to_name n t_path) regex ^
              tyexp_rec s4 s5 fields s6 ^
              T.typedefrec_end
          | _ -> assert false
      end

  | Val_def (Let_def(s1, targets,(p, name_map, topt,sk, e)),tnvs,class_constraints) ->
      let is_simple = true in
      if in_target targets then 
        ws s1 ^ kwd (if is_simple then "definition" else "fun") ^ 
        (if T.target = Target_ident then
           targets_opt targets 
         else
           emp) ^
        isa_mk_typed_def_header (pat p, [], sk, exp_to_typ e) ^
        kwd "where \n\"" ^ pat p ^ ws sk ^ kwd "= (" ^ exp e ^ kwd ")\"" ^ T.def_end ^
        (match val_def_get_name d with None -> emp | Some n ->
          (if is_simple then emp else 
                          (kwd (String.concat "" ["\ndeclare "; Name.to_string n; ".simps [simp del]"]))))
      else emp
  
  | Val_def (Fun_def (s1, rec_flag, targets, clauses),tnvs,class_constraints) ->
      let (_, is_rec) = Typed_ast_syntax.is_recursive_def d in
      if in_target targets then 
        let is_simple = not is_rec && (match Seplist.to_list clauses with
          | [(_, _, ps, _, _, _)] -> List.for_all (fun p -> (Pattern_syntax.is_var_wild_pat p)) ps
          | _ -> false) 
        in
        let s2 = match rec_flag with FR_non_rec -> None | FR_rec sk -> sk in
        ws s1 ^ kwd (if is_rec then "function (sequential)" else (if is_simple then "definition" else "fun")) ^ ws s2 ^
        (if T.target = Target_ident then
           targets_opt targets 
         else
           emp) ^
        (isa_funcl_header_seplist clauses) ^
        flat (Seplist.to_sep_list (isa_funcl_default (kwd "= ")) (sep T.def_sep) clauses) ^
        (if is_rec then (kwd "\nby pat_completeness auto") else emp) ^
        (match val_def_get_name d with None -> emp | Some n ->
          (if is_rec || is_simple then emp else 
                (kwd (String.concat "" ["\ndeclare "; Name.to_string n; ".simps [simp del]"])))) ^
        new_line
      else emp
      
  | Val_spec(s1,(n,l),n_ref,s2,t) ->
      raise (Reporting_basic.err_todo false l "Isabelle: Top-level type constraints omited; should not occur at the moment")

  (* TODO INDRELN THe names should be output *)
  | Indreln(s,targets,names,clauses) ->
      if in_target targets then
        ws s ^
        T.reln_start ^
        (if T.target = Target_ident then
           targets_opt targets 
         else
           emp) ^
        isa_funcl_header_indrel_seplist clauses ^
        flat (Seplist.to_sep_list indreln_clause (sep T.reln_sep) clauses) ^
        T.reln_end
      else
        emp
        
  | _ -> def_internal callback inside_module d is_user_def

and def callback (inside_module : bool) d is_user_def =
  match T.target with 
   | Target_no_ident Target_isa  -> isa_def callback inside_module d is_user_def
   | Target_no_ident Target_tex  -> 
      meta "\\lemdef{\n" ^ def_internal callback inside_module d is_user_def ^ meta "\n}\n"
   | Target_no_ident Target_html -> html_link_def d ^ def_internal callback inside_module d is_user_def
   | _ -> def_internal callback inside_module d is_user_def


end


module F(T : Target)(A : sig val avoid : var_avoid_f option;; val env : env end)(X : sig val comment_def : def -> Ulib.Text.t end) = struct

let (^^^^) = Ulib.Text.(^^^)

let output_to_rope out = to_rope T.string_quote T.lex_skip T.need_space out

module F' = F_Aux(T)(struct let avoid = A.avoid;; let env = A.env;; let ascii_rep_set = Types.Cdset.empty end)(X)

module C = Exps_in_context (struct
  let env_opt = Some A.env
  let avoid = A.avoid
end);;

module CdsetE = Util.ExtraSet(Types.Cdset)

let exp_to_rope e = output_to_rope (F'.exp e)
let pat_to_rope p = output_to_rope (F'.pat p)
let src_t_to_rope t = output_to_rope (F'.typ t)
let typ_to_rope t = src_t_to_rope (C.t_to_src_t t)

let rec batrope_pair_concat : (Ulib.Text.t * Ulib.Text.t) list -> (Ulib.Text.t * Ulib.Text.t)
  = function
    |  [] -> (r"",r"")
    |  (r1,r2)::rrs  -> let (r1',r2') = batrope_pair_concat rrs in (r1^^^^r1', r2^^^^r2') 

(* for -inc.tex file *)
let defs_inc ((ds:def list),end_lex_skips) =
  match T.target with
  | Target_no_ident Target_tex -> 
      batrope_pair_concat (List.map (function ((d,s),l,lenv) -> 
        let ue = add_def_entities T.target true empty_used_entities ((d,s),l,lenv) in
        let module F' = F_Aux(T)(struct let avoid = A.avoid;; let env = { A.env with local_env = lenv };;
					let ascii_rep_set = CdsetE.from_list ue.used_consts end)(X) in
        batrope_pair_concat (F'.def_tex_inc d)) ds)
  | _ ->
      raise (Failure "defs_inc called on non-tex target")


let rec defs (ds:def list) =
  List.fold_right
    (fun ((d,s),l,lenv) y -> 
       begin
        let ue = add_def_entities T.target true empty_used_entities ((d,s),l,lenv) in
        let module F' = F_Aux(T)(struct let avoid = A.avoid;; let env = { A.env with local_env = lenv };;
					let ascii_rep_set = CdsetE.from_list ue.used_consts end)(X) in
        F'.def defs false d (is_pp_loc l)
       end ^

       begin
         match s with
           | None ->
               emp
           | Some(s) -> 
               ws s ^ kwd ";;"
       end ^
       y)
    ds 
    emp

let defs_to_rope ((ds:def list),end_lex_skips) =
  match T.target with
  | Target_no_ident Target_tex -> 
      (to_rope_tex (defs ds) ^^^^
      (match to_rope_option_tex (ws end_lex_skips) with None -> r"" | Some rr -> 
        r"\\lemdef{\n" ^^^^
        rr  ^^^^
        r"\n}\n"
      ))
  | _ -> output_to_rope (defs ds ^ ws end_lex_skips)

let defs_to_extra_aux gf (ds:def list) =
    List.fold_right
      (fun ((d,s),l,lenv) y -> 
         begin
           let ue = add_def_entities T.target true empty_used_entities ((d,s),l,lenv) in
           let module F' = F_Aux(T)(struct let avoid = A.avoid;; let env = { A.env with local_env = lenv };;
                                           let ascii_rep_set = CdsetE.from_list ue.used_consts end)(X) in
           match T.target with 
           | Target_no_ident Target_isa   -> F'.isa_def_extra gf d l 
           | Target_no_ident Target_hol   -> F'.hol_def_extra gf d l 
           | Target_no_ident Target_ocaml -> F'.ocaml_def_extra gf d l 
           | _ -> emp
         end ^

         begin
           match s with
             | None ->
                 emp
             | Some(s) -> 
                 ws s 
         end ^
       y)
      ds 
    emp 

let defs_to_extra ((ds:def list), end_lex_skips) =
begin
  let gf_termination =
     {extra_gen_termination = (!gen_extra_level > 1);
      extra_gen_asserts     = false;
      extra_gen_lemmata     = false;
      extra_gen_theorems    = false} in
  let gf_assert =
     {extra_gen_termination = false;
      extra_gen_asserts     = (!gen_extra_level > 0);
      extra_gen_lemmata     = false;
      extra_gen_theorems    = false} in
  let gf_lemmata =
     {extra_gen_termination = false;
      extra_gen_asserts     = false;
      extra_gen_lemmata     = (!gen_extra_level > 1);
      extra_gen_theorems    = (!gen_extra_level > 1)} in

  let out =  (
    prefix_if_not_emp (new_line ^ comment_block (Some 50) ["";"Assertions"; ""])
      (defs_to_extra_aux gf_assert ds)  ^

    prefix_if_not_emp (new_line ^ comment_block (Some 50) ["";"Termination Proofs";""])
      (defs_to_extra_aux gf_termination ds)  ^

    prefix_if_not_emp (new_line ^ comment_block (Some 50) ["";"Lemmata";""])
      (defs_to_extra_aux gf_lemmata ds))

  in
  if (out = emp) then None else
    Some (output_to_rope (out ^ new_line ^ new_line))
end

let header_defs ((defs:def list),(end_lex_skips : Typed_ast.lskips)) =  
  to_rope T.string_quote T.lex_skip T.need_space
    (List.fold_right 
       (fun ((d,s),l,lenv) y ->
          let module B = Backend_common.Make (struct
            let env = { A.env with local_env = lenv }
            let target = T.target
            let id_format_args =  (T.op_format, T.path_sep)    
          end) in
          begin match T.target with

              Target_no_ident Target_isa -> 
                begin 
                  match d with 
                      OpenImport((Ast.OI_open s | Ast.OI_open_import (s, _)),ms) -> 
                        Output.flat (List.map (fun m ->                        
                          kwd "\t \""^Ident.to_output Module_name T.path_sep (B.module_id_to_ident m)^kwd "\"") ms)
                    | _ -> emp
                end

            | _ -> emp
          end ^ 
          y)
       defs 
       emp)
end

module Make(A : sig val avoid : var_avoid_f;; val env : env end) = struct
  module Dummy = struct let comment_def d = assert false end

  module C = struct let env = A.env;; let avoid = Some(A.avoid) end

  let ident_defs defs =
    let module B = F(Identity)(C)(Dummy) in
      B.defs_to_rope defs

  let html_defs defs =
    let module B = F(Html)(C)(Dummy) in
      B.defs_to_rope defs

  let tex_defs defs =
    let module B = F(Tex)(C)(Dummy) in
      B.defs_to_rope defs

  let tex_inc_defs defs =
    let module B = F(Tex)(C)(Dummy) in
      B.defs_inc defs

  module Comment_def = struct
    let comment_def d = ident_defs ([d],None)
  end

  let hol_defs defs =
    let module B = F(Hol)(C)(Comment_def) in
      (B.defs_to_rope defs, B.defs_to_extra defs)

  let ocaml_defs defs =
    let module B = F(Ocaml)(C)(Comment_def) in
      (B.defs_to_rope defs, B.defs_to_extra defs)

  let isa_defs defs =
    let module B = F(Isa)(C)(Comment_def) in
      (B.defs_to_rope defs, B.defs_to_extra defs)

  let isa_header_defs defs =
    let module B = F(Isa)(C)(Comment_def) in
      B.header_defs defs

  let coq_defs defs =
    let module B = Coq_backend.CoqBackend (C) in
      B.coq_defs defs

  let ident_exp e = 
    let module B = F(Identity)(C)(Dummy) in
    let (e', _) = alter_init_lskips (fun _ -> (None, None)) e in
    B.exp_to_rope e'

  let ident_pat p = 
    let module B = F(Identity)(C)(Dummy) in
    let (p', _) = pat_alter_init_lskips (fun _ -> (None, None)) p in
    B.pat_to_rope p'

  let ident_src_t t = 
    let module B = F(Identity)(C)(Dummy) in
    B.src_t_to_rope t

  let ident_typ t = 
    let module B = F(Identity)(C)(Dummy) in
    B.typ_to_rope t

  let ident_def d = 
    let (d', _) = def_alter_init_lskips (fun _ -> (None, None)) d in
    ident_defs ([d'], None)

end
