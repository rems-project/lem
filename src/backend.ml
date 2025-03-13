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
(*          Brian Campbell, University of Edinburgh                       *)
(*          Shaked Flur, University of Cambridge                          *)
(*          Thomas Bauereiss, University of Cambridge                     *)
(*          Stephen Kell, University of Cambridge                         *)
(*          Thomas Williams                                               *)
(*          Lars Hupel                                                    *)
(*          Basile Clement                                                *)
(*                                                                        *)
(*  The Lem sources are copyright 2010-2025                               *)
(*  by the authors above and Institut National de Recherche en            *)
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
(*                                                                        *)
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
open Types
open Typed_ast
open Typed_ast_syntax
open Output
open Target

let gen_extra_level = ref 3
let suppress_target_names = ref false
let suppress_libraries = ref false

let r = Ulib.Text.of_latin1
let (^^) = Stdlib.(^)

let gensym_tex_command =
  let n = ref 0 in
  function () ->
    n := 1 + !n;
    tex_command_escape (Ulib.Text.of_string (string_of_int !n))

let rec process_latex_labels s =
  let regexp = Str.regexp "\\([^_]*\\)_+\\(.*\\)" in
  if Str.string_match regexp s 0 then
    let new_s = String.concat "" [Str.matched_group 1 s; String.capitalize_ascii (Str.matched_group 2 s)] in
    process_latex_labels new_s
  else
    s

let reserved_labels = ["type"; "const"; "module"; "rename"; "open"; "instance"; "class"; "declaration"; "comment"]
let latex_fresh_labels = let f = Util.fresh_string reserved_labels  in (fun s -> f (process_latex_labels s))

(* Use SML-style escape sequences for HOL, with some caveats.  See
 * src/parse/MLstring.sml in HOL source code, as well as
 * http://www.standardml.org/Basis/char.html#SIG:CHAR.toString:VAL *)

let char_escape_ocaml c = match int_of_char c with
  | 0x5c -> "\\\\" (* backslash *)
  | 0x22 -> "\\\"" (* double quote *)
  | 0x27 -> "\\\'" (* single quote *)
  | x when x >= 32 && x <= 126 -> (* other printable characters *)
      String.make 1 c
  | 0x07 -> "\\a" (* common control characters *)
  | 0x08 -> "\\b"
  | 0x09 -> "\\t"
  | 0x0a -> "\\n"
  | 0x0b -> "\\v"
  | 0x0c -> "\\f"
  | 0x0d -> "\\r"
  | x when x <= 255 ->
      Printf.sprintf "\\%03u" x
  | _ -> failwith "int_of_char returned an unexpected value"

let char_escape_hol c = match int_of_char c with
  | 0x5c -> "\\\\" (* backslash *)
  | 0x22 -> "\\\"" (* double quote *)
  | 0x5e -> "\094" (* carret *)
  | 0x60 -> "\096" (* back quote *)
  | x when x >= 32 && x <= 126 -> (* other printable characters *)
      String.make 1 c
  | 0x07 -> "\\a" (* common control characters *)
  | 0x08 -> "\\b"
  | 0x09 -> "\\t"
  | 0x0a -> "\\n"
  | 0x0b -> "\\v"
  | 0x0c -> "\\f"
  | 0x0d -> "\\r"
  | x when (x >= 0 && x < 32) (* other control characters *)
        || (x > 126 && x <= 255) ->
      Printf.sprintf "\\%03u" x
  | _ -> failwith "int_of_char returned an unexpected value"

let string_escape_hol s =
  let b = Buffer.create (String.length s) in
  (* Do not iterate on the UTF8 code, because HOL does not handle UTF8 even
   * though SML does, for some reason. *)
  String.iter (fun c -> Buffer.add_string b (char_escape_hol c)) s;
  Buffer.contents b

(* check whether a character is natively supported by Isabelle *)
let is_isa_chr x =
  x >= 0x20 && x <= 0x7e &&
  (* most printable characters are supported, but there are some exceptions! *)
  not (List.mem x [0x22; 0x27; 0x5c; 0x60])

let char_escape_isa c =
  let x = int_of_char c in
  if is_isa_chr x then (String.concat "" ["(CHR ''"; String.make 1 c; "'')"])
  else String.concat "" ["(CHR "; Printf.sprintf "0x%X" x; ")"];;

(* Check that string literal s contains only CHR characters for Isabelle.  Other
 * string literals should have been translated into a list by a macro. *)
let string_escape_isa s =
  let is_isa_chr c =
    let x = int_of_char c in
    (x >= 0x20 && x <= 0x7e &&
     (* most printable characters are supported, but there are some exceptions! *)
     not (List.mem x [0x22; 0x27; 0x5c; 0x60])) in
  let is_simple_is_string = Util.string_for_all is_isa_chr s in
  if is_simple_is_string then
    String.concat "" ["(''"; s; "'')"]
  else
    let char_list = Util.string_to_list s in
    let encoded_chars = List.map char_escape_isa char_list in
    String.concat "" ["(["; String.concat ", " encoded_chars; "])"]

let pat_add_op_suc kwd suc n s1 s2 i =
  let rec suc_aux j =
    if Z.leq j Z.zero then n else
    kwd "(" ^ suc ^ suc_aux (Z.pred j) ^ kwd ")"
  in
  ws s1 ^ ws s2 ^ (suc_aux i)

  let const_char_helper c c_org =
     (String.concat "" ["#\'"; Util.option_default (char_escape_ocaml c) c_org; "\'"])


type cerberus_exp_or_pat_kind =
  | Plain
  | Core
  | Ail

module type Target = sig
  val lex_skip : Ast.lex_skip -> Ulib.Text.t
  val bkwd : string -> Output.t
  val ckwd : string -> Output.t  (* for Cerberus core keywords *)
  val akwd : string -> Output.t  (* for Cerberus ail keywords *)
  val asbr : cerberus_exp_or_pat_kind -> Output.t -> Output.t  (* for Cerberus ail semantic brackets *)
  val need_space : Output.t' -> Output.t' -> bool

  val target : Target.target

  val path_sep : Ulib.Text.t
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
  val typ_class_constraint_prefix_end : t
  val typ_with_sort : t -> Ulib.Text.t -> t

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
  val string_escape : Ulib.UTF8.t -> Ulib.UTF8.t option -> Ulib.UTF8.t
  val const_char : char -> string option -> t
  val const_undefined : Types.t -> string -> t
  val const_bzero : t
  val const_bone : t
  (* The Boolean parameter for the following two indicates whether the number
   * comes from L_numeral (as opposed to L_num) *)
  val const_num : bool -> Z.t -> string option -> t
  val const_num_pat : bool -> Z.t -> t

  (* Expressions *)
  val backend_quote : t -> t
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
  val pat_add_op : t -> Ast.lex_skips -> Ast.lex_skips -> Z.t -> t
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
  val targets_opt_start : t
  val targets_opt_start_neg : t
  val targets_opt_end : t

  (* Value definitions *)
  val def_start : t
  val def_binding : t
  val def_end : t
  val def_sep : t
  val name_start : t
  val name_end : t
  val rec_def_header : bool -> bool -> bool -> lskips -> lskips -> Name.t list -> t
    (** [rec_def_header is_rec is_real_rec try_term sk1 sk2 n] formats [let sk1 rec? sk2 n].
        The flag [is_rec] denotes whether the keyword [rec] occours in the input, while
        [is_real_rec] denotes whether the definition is really recursive. [try_term] signals, whether
        an automatic termination proof should be attempted*)
  val rec_def_footer : bool -> bool -> bool -> Name.t list -> t
  val funcase_start : t
  val funcase_end : t
  val reln_start : t
  val reln_show_types : bool
  val reln_end : t
  val reln_sep : t
  val reln_name_start : t
  val reln_name_end : t
  val reln_clause_sep : t
  val reln_clause_start : t
  val reln_clause_quant : t
  val reln_clause_show_empty_quant : bool
  val reln_clause_show_name : bool
  val reln_clause_quote_name : bool
  val reln_clause_add_paren : bool
  val reln_clause_end : t

  (* Type defnitions *)
  val typedef_start : bool -> t
  val typedef_binding : t
  val typedef_end : bool -> t
  val typedef_sep : t
  val typedefrec_start : bool -> t
  val typedefrec_end : bool -> t

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
  val module_include : t
  val module_only_single_open : bool
end


module Identity : Target = struct
  open Str

  let lex_skip = function
    | Ast.Com(r) -> ml_comment_to_rope r
    | Ast.Ws(r) -> r
    | Ast.Nl -> r"\n"

  module S = Set.Make(String)

  let bkwd = kwd
  let ckwd = kwd
  let akwd = kwd
  let asbr kind output = kwd "[[" ^ output ^ kwd "]]"

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

  let path_sep = r "."
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
  let typ_class_constraint_prefix_end = kwd "=>"
  let typ_with_sort _ _ = err "Type with sort not supported in ident backend"

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
  let string_escape s s_org = Util.option_default (String.escaped s) s_org
  let const_num _ i i_opt = Util.option_default_map i_opt (num i) kwd
  let const_num_pat _ = num
  let const_char c c_org = kwd (const_char_helper c c_org)
  let const_undefined t m = (kwd "Undef") (* ^ (comment m) *)
  let const_bzero = kwd "#0"
  let const_bone = kwd "#1"

  let backend_quote i = (meta "`") ^ i ^ (meta "`")
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
  let pat_add_op n s1 s2 i =  n ^ ws s1 ^ (kwd "+") ^ ws s2 ^ const_num true i None
  let set_sep = kwd ";"
  let list_begin = kwd "["
  let list_end = kwd "]"
  let vector_begin = kwd "[|"
  let vector_end = kwd "|]"
  let first_case_sep = Seplist.Optional

  let tup_sep = kwd ","
  let targets_opt_start = meta "{"
  let targets_opt_start_neg = meta "~{"
  let targets_opt_end = meta "}"

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
  let rec_def_header rr rrr _ sk1 sk2 _ =  ws sk1 ^ kwd "let" ^ ws sk2 ^ (if (rr || rrr) then kwd "rec" else emp)
  let rec_def_footer _ _ _ n = emp
  let funcase_start = emp
  let funcase_end = emp
  let reln_start = kwd "indreln"
  let reln_show_types = true
  let reln_end = emp
  let reln_sep = kwd "and"
  let reln_name_start = kwd "["
  let reln_name_end = kwd "]"
  let reln_clause_sep = kwd "==>"
  let reln_clause_quant = kwd "forall"
  let reln_clause_show_empty_quant = true
  let reln_clause_show_name = true
  let reln_clause_quote_name = false
  let reln_clause_add_paren = false
  let reln_clause_start = emp
  let reln_clause_end = emp

  let typedef_start _ = kwd "type"
  let typedef_binding = kwd "="
  let typedef_end _ = emp
  let typedef_sep = kwd "and"
  let typedefrec_start _ = kwd "type"
  let typedefrec_end _ = emp
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
  let module_include = kwd "include"
  let module_only_single_open = false
end

module Html : Target = struct
  include Identity
  let target = Target_no_ident Target_html

  let bkwd s = kwd (String.concat "" ["<b>";s;"</b>"])
  let ckwd s = kwd (String.concat "" ["<b><font color=\"blue\">"; s;  "</font></b>"])
  let akwd s = kwd (String.concat "" ["<b><font color=\"magenta\">"; s;  "</font></b>"])
  let asbr kind output =
    match kind with
    | Plain -> kwd "[[" ^ output ^ kwd "]]"
    | Ail -> kwd "<font color=\"magenta\">[[</font>" ^ output ^ kwd "<font color =\"magenta\">]]</font>"
    | Core -> kwd "<font color=\"blue\">[[</font>" ^ output ^ kwd "<font color =\"blue\">]]</font>"


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

  let typ_with_sort _ _ = err "Type with sort not supported in HTML backend"

  let backend_quote i = (meta "`") ^ i ^ (meta "`")
end

module Lem : Target = struct
  include Identity
  let target = Target_no_ident Target_lem

  let backend_quote i = (meta "`") ^ i ^ (meta "`")
end

module Tex : Target = struct
  open Str

  let lex_skip = function _ -> r"DUMMY"

  module S = Set.Make(String)

  let need_space = Identity.need_space
  let target = Target_no_ident Target_tex

  let bkwd s = kwd (String.concat "" ["\\lemkw{"; Ulib.Text.to_string (tex_escape (Ulib.Text.of_string s));  "}"])

  let ckwd s = kwd (String.concat "" ["{\\color{blue}{\\lemkw{"; Ulib.Text.to_string (tex_escape (Ulib.Text.of_string s));  "}}}"])

  let akwd s = kwd (String.concat "" ["{\\color{magenta}{\\lemkwtt{"; Ulib.Text.to_string (tex_escape (Ulib.Text.of_string s));  "}}}"])

  let asbr kind output =
    match kind with
    | Plain -> kwd "[\\![" ^ output ^ kwd "]\\!]"
    | Ail ->  kwd "{\\color{magenta}{[\\![}}" ^ output ^ kwd "{\\color{magenta}{]\\!]}}"
    | Core ->  kwd "{\\color{blue}{[\\![}}" ^ output ^ kwd "{\\color{blue}{]\\!]}}"



  let path_sep = r "." (* "`" *)
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
  let typ_rec_start = kwd "\\lemlrec "
  let typ_rec_end = kwd "\\lemrrec "
  let typ_rec_sep = kwd ";\\,"
  let typ_constr_sep = bkwd "of"
  let typ_var = r""
  let typ_class_constraint_prefix_end = kwd "\\Rightarrow"
  let typ_with_sort _ _ = err "Type with sort not supported in TeX backend"

  let nexp_start = emp
  let nexp_end = emp
  let nexp_var = r"''"
  let nexp_plus = kwd "+"
  let nexp_times = kwd "*"

  let pat_as = bkwd "as"
  let pat_rec_start = kwd "\\lemlrec"
  let pat_rec_end = kwd "\\lemrrec"
  let pat_wildcard = kwd "\\_"

  let const_true = bkwd "true"
  let const_false = bkwd "false"
  let string_quote = r"\""
  let string_escape = Identity.string_escape
  let const_num = Identity.const_num
  let const_num_pat _ = num
  let const_char = function c -> function c_org -> kwd (Output.tex_escape_string (const_char_helper c c_org))
  let const_undefined t m = (bkwd "undefined")
  let const_bzero = kwd "\\#0"
  let const_bone = kwd "\\#1"

  let backend_quote i = i (* quotation done by latex-macro *)
  let case_start = bkwd "match"
  let case_sep1 = bkwd "with"
  let case_sep2 = kwd "|" ^ texspace
  let case_line_sep = kwd "\\rightarrow"
  let case_end = bkwd "end"
  let cond_if = bkwd "if"
  let cond_then = bkwd "then"
  let cond_else = bkwd "else"
  let field_access_start = kwd "."
  let field_access_end = emp
  let fun_start = emp
  let fun_end = emp
  let fun_kwd = bkwd "fun"
  let fun_sep = kwd "\\rightarrow"
  let function_start = bkwd "function"
  let function_end = bkwd "end"
  let record_assign = kwd "="
  let recup_start = kwd "\\lemlrec"
  let recup_middle = bkwd "with"
  let recup_end = kwd "\\lemrrec"
  let recup_assign = kwd "="
  let rec_literal_start = kwd "\\lemlrec"
  let rec_literal_end = kwd "\\lemrrec "
  let rec_literal_sep = kwd ";\\,"
  let rec_literal_assign = kwd "="
  let val_start = bkwd "val"
  let let_start = bkwd "let"
  let let_in = bkwd "in"
  let let_end = emp
  let begin_kwd = bkwd "begin"
  let end_kwd = bkwd "end"
  let forall = kwd "\\forall"
  let exists = kwd "\\exists"
  let set_quant_binding = kwd "\\mathord{\\in} "
  let list_quant_binding = bkwd "mem"
  let quant_binding_start = emp (* kwd "("*)
  let quant_binding_end = emp (* kwd ")"*)
  let set_start = kwd "\\{"
  let set_end = kwd "\\}"
  let setcomp_binding_start = kwd "\\forall"
  let setcomp_binding_sep = emp
  let setcomp_binding_middle = texspace ^ kwd "|" ^ texspace
  let setcomp_sep = texspace ^ kwd "|" ^ texspace
  let cons_op = kwd "::"
  let pat_add_op n s1 s2 i =  n ^ ws s1 ^ kwd "+" ^ ws s2 ^ const_num true i None
  let set_sep = kwd ",\\,"
  let list_begin = kwd "["
  let list_end = kwd "]"
  let vector_begin = kwd "[|"
  let vector_end = kwd "|]"
  let first_case_sep = Seplist.Optional
  let op_format = Identity.op_format

  let tup_sep = kwd ",\\,"
  let targets_opt_start = meta "\\{"
  let targets_opt_start_neg = meta "\\sim\\!\\{"
  let targets_opt_end = meta "\\}"

  let def_start = bkwd "let"
  let def_binding = kwd "="
  let def_end = emp
  let name_start = kwd "["
  let name_end = kwd "]"
  let def_sep = kwd "|"
  let rec_def_header _ rrr _ sk1 sk2 _ = ws sk1 ^ bkwd "let" ^ ws sk2 ^ (if rrr then bkwd "rec" else emp)
  let rec_def_footer _ _ _ n = emp
  let funcase_start = emp
  let funcase_end = emp
  let reln_start = bkwd "indreln"
  let reln_show_types = true
  let reln_end = emp
  let reln_sep = bkwd "and"
  let reln_name_start = kwd "["
  let reln_name_end = kwd "]"
  let reln_clause_sep = kwd "\\Longrightarrow"
  let reln_clause_start = emp
  let reln_clause_quant = kwd "\\forall"
  let reln_clause_show_empty_quant = true
  let reln_clause_show_name = true
  let reln_clause_quote_name = false
  let reln_clause_add_paren = false
  let reln_clause_end = emp

  let typedef_start _ = bkwd "type"
  let typedef_binding = kwd "="
  let typedef_end _ = emp
  let typedef_sep = bkwd "and"
  let typedefrec_start _ = bkwd "type"
  let typedefrec_end _ = emp
  let typedefrec_implicits _ = emp
  let rec_start = kwd "\\lemlrec"
  let rec_end = kwd "\\lemrrec"
  let rec_sep = kwd ";"
  let constr_sep = kwd "*"
  let before_tyvars = emp
  let after_tyvars = emp
  let type_abbrev_start = bkwd "type"
  let last_rec_sep = Seplist.Optional
  let last_list_sep = Seplist.Optional
  let last_set_sep = Seplist.Optional
  let first_variant_sep = Seplist.Optional
  let type_params_pre = false
  let nexp_params_vis = true
  let type_abbrev_sep = kwd "="
  let type_abbrev_end = emp
  let type_abbrev_name_quoted = false

  let module_module = bkwd "module"
  let module_struct = bkwd "struct"
  let module_end = bkwd "end"
  let module_open = bkwd "open"
  let module_import = bkwd "import"
  let module_include = bkwd "include"
  let module_only_single_open = false
end


module Ocaml : Target = struct
  include Identity

  let target = Target_no_ident Target_ocaml

  let path_sep = r "."
  let backend_quote i = (meta "`") ^ i ^ (meta "`")

  let typ_rec_start = kwd "{"
  let typ_rec_end = kwd "}"
  let nexp_start = kwd "(*"
  let nexp_end = kwd "*)"
  let nexp_var = r""
  let typ_with_sort _ _ = err "Type with sort not supported in OCaml backend"

  let ctor_typ_end _ _ = emp
  let ctor_typ_end' _ _ _ = emp

  let pat_rec_start = kwd "{"
  let pat_rec_end = kwd "}"
  let pat_wildcard = kwd "_"

  let pat_add_op n s1 s2 i = err "add pattern in Ocaml"

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
  let const_undefined t m = (kwd "failwith ") ^ (str (r m))
  let const_char c c_org =
    meta (String.concat "" ["\'"; (char_escape_ocaml c); "\'"])
  let const_num is_numeral i i_opt =
    if is_numeral then
      if Z.numbits i < 31
      then kwd "(Nat_big_num.of_int" ^ space ^ Identity.const_num true i i_opt ^ kwd ")"
      else kwd "(Nat_big_num.of_string" ^ space ^ str (Ulib.Text.of_string (Z.to_string i)) ^ kwd ")"
    else Identity.const_num false i i_opt
  let rec_start = kwd "{"
  let rec_end = kwd "}"

  let def_sep = kwd "and"
  let name_start = kwd "(*"
  let name_end = kwd "*)"
  let type_params_pre = true
  let nexp_params_vis = false

  let inl = Ident.mk_ident_strings [] "Inl"
  let inr = Ident.mk_ident_strings [] "Inr"

  let module_only_single_open = true
end

let back_tick = List.hd (Ulib.Text.explode (r"`"))
let quotation_mark = List.hd (Ulib.Text.explode (r"\""))
let backslash = List.hd (Ulib.Text.explode (r"\\"))

module Isa () : Target = struct
  include Identity

  let lex_skip = function
    | Ast.Com(r') ->
        let wrap_cartouche x = Ulib.Text.concat (r"") [r"\\<open>"; x; r"\\<close>"] in
        let comment = r"\\<comment> " in
        let rec ml_comment_to_rope = function
        | Ast.Chars(r) -> r
        | Ast.Comment(coms) -> wrap_cartouche (Ulib.Text.concat (r"") (List.map ml_comment_to_rope coms))
        in
          Ulib.Text.append comment (wrap_cartouche (ml_comment_to_rope r'))
    | Ast.Ws(r) -> r
    | Ast.Nl -> r"\n"

  let target = Target_no_ident Target_isa

  (* TODO : write need_space *)

  let path_sep = r "."
  let list_sep = kwd ","
  let backend_quote i = (meta "`") ^ i ^ (meta "`")

  let ctor_typ_end _ _ = emp
  let ctor_typ_end' _ _ _ = emp

  let typ_start = kwd "\""
  let typ_end = kwd "\""
  let typ_tup_sep = kwd "*"
  let typ_tup_section = emp
  let typ_sep = kwd "::"
  let typ_fun_sep = kwd "\\<Rightarrow>"
  let typ_rec_start = kwd "\n"
  let typ_rec_end = kwd "\n"
  let typ_rec_sep = kwd "\n"
  let typ_constr_sep = emp
  let typ_var = r"'"
  let typ_class_constraint_prefix_end = kwd "=>"
  let typ_with_sort t sort = kwd "(" ^ t ^ kwd "::" ^ str sort ^ kwd ")"

  let pat_as = err "as pattern in Isabelle"
  let pat_rec_start = err "record pattern in Isabelle"
  let pat_rec_end = err "record pattern in Isabelle"

  let const_true = kwd "True"
  let const_false = kwd "False"
  let string_quote = r""
  let string_escape s _ = string_escape_isa s
  let const_num _ i i_opt = match i_opt with
    | Some s ->
       Str.replace_first (Str.regexp "^0X") "0x" s
       |> Str.replace_first (Str.regexp "^0B") "0b"
       |> kwd
    | None -> num i
  let const_num_pat _ i = pat_add_op_suc kwd (kwd "Suc") (kwd "0") None None i
  let const_char c _ = kwd (char_escape_isa c)
  let const_unit s = kwd "() " ^ ws s
  let const_empty s = kwd "{}" ^ ws s
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
  let fun_kwd = meta "\\<lambda>"
  let fun_sep = meta ". "

  let record_assign = kwd "="
  let recup_start = kwd "("
  let recup_middle = kwd "(|"
  let recup_end = kwd "|)" ^ kwd ")"
  let recup_assign = kwd ":="

  let val_start = kwd "val" (* TODO*)
  let let_start = kwd "(" ^ kwd "let"
  let let_end = kwd ")"

  let begin_kwd = kwd "("
  let end_kwd = kwd ")"

  let forall = kwd "\\<forall>"
  let exists = kwd "\\<exists>"

  let set_quant_binding = kwd "\\<in>"
  let quant_binding_start = emp
  let quant_binding_end = emp

  let set_start = kwd "{"
  let set_end = kwd "}"
  let setcomp_binding_start = emp
  let setcomp_binding_sep = kwd " "
  let setcomp_binding_middle = kwd "."
  let setcomp_sep = kwd "|"
  let first_case_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")

  let star = Ulib.Text.of_latin1 "*"
  let space = Output.ws (Some [Ast.Ws (Ulib.Text.of_latin1 " ")])
  let infix_op_format a x = match a with (Term_var | Term_var_toplevel) -> id a x | _ -> kwd "(" ^ id a x ^ kwd ")"

  let op_format use_infix = if use_infix then infix_op_format else id

  let pat_add_op n s1 s2 i = pat_add_op_suc kwd (kwd "Suc") n s1 s2 i
  let cons_op = kwd "#"
  let set_sep = kwd ","

  let def_start = kwd "definition"
  let def_end = emp

  let def_sep = kwd "|"
  let rec_def_header _ rr try_term sk1 sk2 _ = (if (rr && not try_term) then kwd "function (sequential)" else kwd "fun") ^ ws sk1 ^ ws sk2
  let rec_def_footer _ rr try_term n = if (rr && not try_term) then kwd "by pat_completeness auto" else emp

  let funcase_start = emp
  let funcase_end = emp
  let reln_start = kwd "inductive"
  let reln_show_types = true
  let reln_end = emp
  let reln_sep = kwd "|"
  let reln_name_start = emp (*TODO Indreln fix up for isabelle*)
  let reln_name_end = emp
  let reln_clause_start = kwd "\""
  let reln_clause_quant = kwd "\\<And>"
  let reln_clause_show_empty_quant = false
  let reln_clause_show_name = true
  let reln_clause_quote_name = true
  let reln_clause_add_paren = false
  let reln_clause_end = kwd "\""

  let typedef_start has_sort =
    if has_sort then
      meta "context notes [[typedef_overloaded]] begin" ^
      new_line ^
      kwd "datatype"
    else
      kwd "datatype"
  let typedef_end has_sort =
    if has_sort then
      new_line ^ meta "end"
    else
      emp
  let typedef_sep = kwd "and"

  let typedefrec_start has_sort =
    if !Backend_common.isa_use_datatype_record_flag then
      if has_sort then
        meta "context notes [[typedef_overloaded]] begin" ^
        new_line ^
        kwd "datatype_record"
      else
        kwd "datatype_record"
    else
      if has_sort then
        kwd "record (overloaded)"
      else
        kwd "record"
  let typedefrec_end has_sort =
    if !Backend_common.isa_use_datatype_record_flag && has_sort then
      meta "end" ^ new_line
    else
      emp
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
  let module_only_single_open = false
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
  let bkwd = kwd
  let ckwd = kwd
  let akwd = kwd
  let asbr kind output = output

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

  let path_sep = r "$"
  let list_sep = kwd ";"
  let backend_quote i = (meta "`") ^ i ^ (meta "`")

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
  let typ_class_constraint_prefix_end = kwd "=>"
  let typ_with_sort _ _ = err "Type with sort not supported in HOL backend"

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
  let string_escape s _ = string_escape_hol s
  let const_num _ i i_opt = match i_opt with
    | Some s ->
       Str.replace_first (Str.regexp "^0X") "0x" s
       |> Str.replace_first (Str.regexp "^0B") "0b"
       |> kwd
    | None -> num i
  let const_num_pat _ i = pat_add_op_suc kwd (kwd "SUC") (kwd "0") None None i
  let const_char c _ = meta (String.concat "" ["#\""; char_escape_hol c; "\""])
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
  let fun_kwd = meta "\\"
  let fun_sep = meta ". "
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
  let pat_add_op n s1 s2 i = pat_add_op_suc kwd (kwd "SUC") n s1 s2 i
  let cons_op = kwd "::"
  let set_sep = kwd ";"
  let list_begin = kwd "["
  let list_end = kwd "]"
  let vector_begin = emp
  let vector_end = emp
  let first_case_sep = Seplist.Forbid(fun sk -> ws sk ^ meta " ")
  let star = Ulib.Text.of_latin1 "*"
  let space = Output.ws (Some [Ast.Ws (Ulib.Text.of_latin1 " ")])
  let infix_op_format a x = match a with (Term_var | Term_var_toplevel) -> id a x | _ -> begin
     if (Ulib.Text.left x 1 = star || Ulib.Text.right x 1 = star) then
       kwd "(" ^ space ^ id a x ^ space ^ kwd ")"
     else
       kwd "(" ^ id a x ^ kwd ")"
  end
  let op_format use_infix = if use_infix then infix_op_format else id

  let tup_sep = kwd ","
  let targets_opt_start = meta "{"
  let targets_opt_start_neg = meta "~{"
  let targets_opt_end = meta "}"

  let def_start = meta "val _ = Define `\n"
  let def_binding = kwd "="
  let def_end = meta "`;\n"
  let def_sep = kwd "/\\"
  let name_start = kwd "(*"
  let name_end = kwd "*)"
  let rec_def_header _ rrr try_term sk1 sk2 ns = match ns with
    | [] ->  assert false
    | (l::ls) -> ws sk1 ^ ws sk2 ^
              let n = Ulib.Text.to_string (Name.to_rope l) in
              if (rrr && not try_term) then
                if (List.length ls = 0) then
                  meta (Format.sprintf "val %s_defn = Hol_defn \"%s\" `\n" n n)
                else
                  meta (Format.sprintf "val %s_defn = Defn.Hol_multi_defns `\n" n)
              else
                meta (Format.sprintf "val _ = Define `\n")
  let rec_def_footer _ rrr try_term ns = match ns with
    | [] ->  assert false
    | (n::ns) -> let n = Ulib.Text.to_string (Name.to_rope n) in
              if (rrr && not try_term) then
                if (List.length ns == 0) then
                  meta (Format.sprintf "\nval _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn %s_defn;" n)
                else
                  meta (Format.sprintf "\nval _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) %s_defn;" n)
              else emp
  let funcase_start = kwd "("
  let funcase_end = kwd ")"
  let reln_start = meta "val _ = Hol_reln `"
  let reln_show_types = false
  let reln_end = meta "`;"
  let reln_sep = kwd "/\\"
  let reln_name_start = emp (*TODO Inderln fixup for Hol*)
  let reln_name_end = emp
  let reln_clause_sep = kwd "==>"
  let reln_clause_start = kwd "("
  let reln_clause_quant = kwd "!"
  let reln_clause_show_empty_quant = false
  let reln_clause_show_name = false
  let reln_clause_quote_name = false
  let reln_clause_add_paren = true
  let reln_clause_end = kwd ")"

  let typedef_start _ = meta "val _ = Hol_datatype `\n"
  let typedef_binding = kwd "="
  let typedef_end _ = meta "`;\n"
  let typedef_sep = kwd ";"
  let typedefrec_start _ = meta "val _ = Hol_datatype `\n"
  let typedefrec_end _ = meta "`;\n"
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
  let module_include = kwd "include"
  let module_only_single_open = false
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


module F_Aux(T : Target)(A : sig val avoid : var_avoid_f option;; val env : env;; val ascii_rep_set : Types.Cdset.t;; val dir : string end)(X : sig val comment_def : def -> Ulib.Text.t end) = struct

module B = Backend_common.Make (struct
  let env = A.env
  let target = T.target
  let id_format_args =  (T.op_format, T.path_sep)
  let dir = A.dir
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

let lit l is_pat t = match l.term with
  | L_true(s) -> ws s ^ T.const_true
  | L_false(s) -> ws s ^ T.const_false
  | L_undefined(s,m) -> ws s ^ T.const_undefined t m
  | L_num(s,i,org_input) -> ws s ^ (if is_pat then T.const_num_pat false i else T.const_num false i org_input)
  | L_numeral(s,i,org_i) -> ws s ^ (if is_pat then T.const_num_pat true  i else T.const_num true  i org_i)
  | L_char(s,c,org_c) -> ws s ^ T.const_char c org_c
  | L_string(s,i,org_i) -> ws s ^ str (Ulib.Text.of_string (T.string_escape i org_i))
  | L_unit(s1,s2) -> ws s1 ^ T.const_unit s2
  | L_zero(s) -> ws s ^ T.const_bzero
  | L_one(s) -> ws s ^ T.const_bone
  | L_vector(s,p,b) -> ws s ^ kwd (String.concat "" [p;b])

let nexp n =
  let rec nexp_int n = match n.nterm with
    | Nexp_var(s,v) ->
        ws s ^ id Nexpr_var (Ulib.Text.(^^^) T.nexp_var (Nvar.to_rope v))
    | Nexp_const(s,i) ->
        ws s ^ T.const_num false i None
    | Nexp_mult(n1,s,n2) ->
        nexp_int n1 ^ ws s ^ T.nexp_times ^ nexp_int n2
    | Nexp_add(n1,s,n2) ->
        nexp_int n1 ^ ws s ^ T.nexp_plus ^ nexp_int n2
    | Nexp_paren(s1,n,s2) ->
        ws s1 ^ kwd "(" ^ nexp_int n ^ ws s2 ^ kwd ")"
  in T.nexp_start ^ nexp_int n ^ T.nexp_end

let rec typ print_backend t = match t.term with
  | Typ_wild(s) ->
      ws s ^ kwd "_"
  | Typ_var(s,v) ->
      ws s ^ id Type_var (Ulib.Text.(^^^) T.typ_var (Tyvar.to_rope v))
  | Typ_fn(t1,s,t2) ->
      typ print_backend t1 ^
      ws s ^
      T.typ_fun_sep ^
      typ print_backend t2
  | Typ_tup(ts) ->
      flat (Seplist.to_sep_list (typ print_backend) (sep T.typ_tup_sep) ts) ^ T.typ_tup_section
  | (Typ_app(p, ts) | Typ_backend(p, ts)) ->
      let (ts', p_out) = begin
        match t.term with
          | Typ_app _ -> B.type_app_to_output (typ print_backend) p ts
          | Typ_backend _ -> (ts,
	      let i = Path.to_ident (ident_get_lskip p) p.descr in
              let i_out = (Ident.to_output (Type_ctor (print_backend, true)) T.path_sep (Ident.replace_lskip i None)) in
              ws (Ident.get_lskip i) ^
              if print_backend then
                T.backend_quote i_out
              else i_out)
          | _ -> raise (Reporting_basic.err_unreachable (Ast.Trans (false, "Backend.typ", None)) "can't be reached because of previous match")
      end in
      if (T.type_params_pre) then
        if (T.nexp_params_vis) then
          bracket_many (typ print_backend) (T.tup_sep) (kwd "(") (kwd ")") ts' ^
          texspace ^ p_out
        else
          bracket_omit (typ print_backend) (fun t f s -> match t.term with
                                        | Typ_len _ -> f t
                                        | _ -> f t ^ s) typ_alter_init_lskips (T.tup_sep) (kwd "(") (kwd ")") ts' ^
          texspace ^ p_out
      else
        p_out ^
        texspace ^
        concat emp (List.map (typ print_backend) ts')
  | Typ_len(n) -> nexp n
  | Typ_paren(s1,t,s2) ->
      ws s1 ^
      kwd "(" ^
      typ print_backend t ^
      ws s2 ^
      kwd ")"
  (* Sorts only appear on type variables *)
  | Typ_with_sort({term = Typ_var _} as t,sort) -> T.typ_with_sort (typ print_backend t) (Name.to_rope sort)
  | Typ_with_sort(t,sort) -> typ print_backend t

let field_ident_to_output cd =
  Ident.to_output Term_field T.path_sep (B.const_id_to_ident cd (use_ascii_rep_for_const cd))
;;

let nk_id_to_output (nk : name_kind id) = match nk.id_path with
  | Id_none sk -> ws sk
  | Id_some i -> (Ident.to_output (Term_const (false, false)) T.path_sep i)


let tyvar tv =
  match tv with
   | Tn_A(s,tv,l) -> ws s ^ id Type_var (Ulib.Text.(^^^) T.typ_var tv)
   | Tn_N(s,nv,l) -> ws s ^ id Nexpr_var (Ulib.Text.(^^^) T.nexp_var nv)

let tyfield print_backend ((n,l),f_ref,s1,t) =
  Name.to_output Term_field (B.const_ref_to_name n false f_ref) ^
  ws s1 ^
  block false 2 (
  T.typ_sep ^
  T.typ_start ^
  block false 0 (typ print_backend t) ^
  T.typ_end)

let tyconstr implicit n' tvs ((n,l),c_ref,s1,targs) =
  Name.to_output (Type_ctor (false, false)) (B.const_ref_to_name n false c_ref) ^
  ws s1 ^
  (if Seplist.length targs = 0 then
     T.ctor_typ_end n' tvs
   else
     T.typ_constr_sep ^
     T.typ_start ^
     flat (Seplist.to_sep_list (typ false) (sep T.constr_sep) targs) ^
     T.ctor_typ_end' implicit n' tvs ^
     T.typ_end ^
     break_hint_space 0 )

let tyexp_abbrev s4 t =
  ws s4 ^
  T.type_abbrev_sep ^
  T.typ_start ^
  typ false t ^
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
          (tyfield false) (sep (T.typ_rec_sep ^ break_hint_space 0)) fields) ^
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

let backend_quote_cond use_quotes o =
  if not use_quotes then o else T.backend_quote o

let backend use_quotes sk i =
  ws sk ^
  backend_quote_cond use_quotes (
    Ident.to_output (Term_const (use_quotes, true)) T.path_sep i)



(* special stuff for Cerberus *)


let normalise_c_id_string c_id_string =
  if String.length c_id_string >=2 && String.sub c_id_string 0 2 = "C." then
    String.concat ""
      ["Core.";  String.sub c_id_string 2 (String.length c_id_string)]
  else
    c_id_string

(* pp something like the (p of (p) but with the lskip of p before the ( *)
let pppat_flip_lskip pppat kw_output p =
  let (p',lskips) = Typed_ast.pat_alter_init_lskips (fun lskips->(Typed_ast.no_lskips, lskips)) p in
  ws lskips ^
  kw_output ^
  pppat p'

let ppexp_flip_lskip ppexp kw_output e =
  let (e',lskips) = Typed_ast.alter_init_lskips (fun lskips->(Typed_ast.no_lskips, lskips)) e in
  ws lskips ^
  kw_output ^
  ppexp e'



(* interleave sp between elements of xs *)
let rec sep_with sp xs = match xs with
| [] -> []
| [x] -> [x]
| x1::x2::xs' -> [x1] @ sp @ sep_with sp (x2::xs')

(* pp of expression lists used in Lem expressions in Core, parameterised by begin/end/separator *)
let exp_core_expr_list pparg es list_begin list_end list_sep last_list_sep =
  match C.exp_to_term es with
  | List(s1,es,s2) ->
      block false 0 (
      ws s1 ^
      list_begin ^
      flat
        (Seplist.to_sep_list_last last_list_sep
           pparg (sep list_sep) es) ^
      ws s2 ^
      list_end)
  | _ -> pparg es (*meta " BACKEND PP FAILURE: exp_core_expr_list" *)

(* pp of expression lists used in Lem expressions in Core pattern positions, mapping Just e to e and Nothing to _ *)
let rec exp_core_expr_option_pattern ppexp e =
  (*meta " CORE_EXPR_OPTION_PATTERN " ^ *)
  match C.exp_to_term e with
  | Constant cd when
      (let (c_descr : Typed_ast.const_descr) = c_env_lookup Ast.Unknown A.env.c_env cd.descr in
      let (c_id_string : string) = Path.to_string c_descr.const_binding in
      String.length c_id_string >=7 && String.sub c_id_string (String.length c_id_string - 7) 7 = "Nothing")
    ->
      let lskip = Typed_ast.ident_get_lskip cd in
      ws lskip ^
      T.ckwd "_"
  | App(e1,e2) ->
      (*meta " APP " ^ *)
      begin
        match C.exp_to_term e1 with
        | Constant cd when
            (let (c_descr : Typed_ast.const_descr) = c_env_lookup Ast.Unknown A.env.c_env cd.descr in
            let (c_id_string : string) = Path.to_string c_descr.const_binding in
            String.length c_id_string >=4 && String.sub c_id_string (String.length c_id_string - 4) 4 = "Just")
          ->
            let lskip = Typed_ast.ident_get_lskip cd in
            ws lskip ^
            ppexp e2
        | _ -> ppexp e
      end
  | Paren(s1,e,s2) ->
      block false 0 (ws s1 ^ T.ckwd "(" ^ block false 0 (exp_core_expr_option_pattern ppexp e ^ ws s2) ^ T.ckwd ")")
  | _ -> (*meta " MISMATCH " ^*)
      ppexp e

let exp_core_expr_pattern_list ppexp es =
  match C.exp_to_term es with
  | List(s1,es,s2) ->
      (match Seplist.is_empty es with
      | true ->
          ws s1 ^
          T.ckwd "_"
      | false ->
          block false 0 (
          ws s1 ^
          T.ckwd "[" ^
          flat
            (Seplist.to_sep_list_last Seplist.Optional
               (exp_core_expr_option_pattern ppexp) (sep (T.ckwd ",")) es) ^
          ws s2 ^
          T.ckwd "]"))
  | _ ->
      (*meta " BACKEND PP FAILURE: core_expr_pattern_list" *)
      ppexp es

(* pp of expression lists used in Lem patterns in Core pattern positions*)

let pat_core_expr_list pppat p list_begin list_end list_sep last_list_sep =
  match p.term with
  | P_list(s1,ps,s2) ->
      ws s1 ^
      list_begin ^
      flat
        (Seplist.to_sep_list_last last_list_sep
           pppat (sep list_sep) ps) ^
      ws s2 ^
      list_end
  | _ -> pppat p (*meta " BACKEND PP FAILURE: pat_core_expr_list" *)

(* using default pp for now for these two*)
let pat_core_expr_option_pattern pppat p =
  pppat p

let pat_core_expr_pattern_list pppat ps =
  pppat ps

let ail_unary_is_postfix c_id_string =
  match c_id_string with
  | "AilSyntax.Plus"        -> false
  | "AilSyntax.Minus"       -> false
  | "AilSyntax.Bnot"        -> false
  | "AilSyntax.Address"     -> false
  | "AilSyntax.Indirection" -> false
  | "AilSyntax.PostfixIncr" -> true
  | "AilSyntax.PostfixDecr" -> true

(* pp of pattern-match clause lists used in Lem expressions in Core *)
let exp_core_clause_list pparg clauses =
  let pp_clause clause =
    match C.exp_to_term clause with
    | Tup(s1,es,s2) ->
        (*block is_user_exp 0*) (
        ws s1 ^
        T.ckwd "|" ^ space ^ (*(pparg e1) ^ T.ckwd "=>" ^ (pparg e2)  ^*)
        flat (Seplist.to_sep_list pparg (sep (flat [space; T.ckwd "=>"; space])) es) ^
        ws s2
       )
    | _ -> pparg clauses (*kwd "ERROR: core_clause_list failed to find Tup of size 2" *)  in
  [exp_core_expr_list pp_clause clauses emp emp emp Seplist.Optional  ]

let pat_core_clause_list clauses pparg =
  []

(* pp of struct member lists used in Lem expressions in Core *)
let exp_core_struct_member_list pparg struct_members =
  let pp_member member =
    match C.exp_to_term member with
    | Tup(s1,es,s2) ->
        (*block is_user_exp 0*) (
        ws s1 ^
        T.ckwd "." ^ (*(pparg e1) ^ T.ckwd "=>" ^ (pparg e2)  ^*)
        flat (Seplist.to_sep_list pparg (sep (flat [space; T.ckwd "="; space])) es) ^
        ws s2
       )
    | _ -> pparg struct_members in
  flat [exp_core_expr_list pp_member struct_members (T.ckwd "{") (T.ckwd "}") (T.ckwd ",") Seplist.Optional  ]

let pat_core_struct_member_list pparg struct_members =
  flat []

let ppcerberus (c_id_string, args) deconstruct_arg pparg pparg_flip_lskip
    core_expr_list core_expr_pattern_list core_expr_option_pattern core_clause_list core_struct_member_list =

  (* Printf.printf "%s\n" c_id_string;*)

  let pparg_flip_lskip_string kw_string e = pparg_flip_lskip (T.akwd kw_string) e in

  let rec ppc (c_id_string, args) =

    let ppc_deconstruct e =   (* deconstruct e and try ppc, falling back to pparg if either fails *)
      match deconstruct_arg e with
      | Some (c_id_string,es) ->
          begin
            match ppc (c_id_string,es) with
            | kind, Some output -> concat emp output
            | kind, None -> pparg e
          end
      | None ->
          pparg e in


    match c_id_string, args with
      (*[meta c_id_string] @ *)

    (** special case for undefined behaviour constructors *)
    | s,[] when String.length s >= 12 && String.sub s 0 12 = "Undefined.UB" -> Core, Some [T.ckwd s]

    (** Core.generic_object_value *)
    | "Core.OVinteger", [mem_integer_value] -> Core, Some [pparg mem_integer_value]
    | "Core.OVfloating", [mem_floating_value] -> Core, Some [pparg mem_floating_value]
    | "Core.OVpointer", [mem_pointer_value] -> Core, Some [pparg mem_pointer_value]
    | "Core.OVcfunction", [nm] -> Core, Some [pparg nm]
    | "Core.OVarray", [vs] -> Core, Some [T.ckwd "array"; core_expr_list vs (T.ckwd "(") (T.ckwd ")") (T.ckwd ",") Seplist.Optional ]
    | "Core.OVstruct", [tag; struct_members] -> Core, Some [T.ckwd "("; T.ckwd "struct"; pparg tag; T.ckwd ")"; core_struct_member_list struct_members]
    | "Core.OVunion", [tag;id;v] -> Core, Some [T.ckwd "("; T.ckwd "union"; space; pparg tag; T.ckwd ")"; T.ckwd "{"; T.ckwd "."; pparg id; T.ckwd "="; pparg v]

    (** Core.generic_value *)
    (* TODO   "Core.Constrained"  *)
    | "Core.Vobject", [v] -> Core, Some [pparg v]
    | "Core.Vspecified", [v] -> Core, Some [T.ckwd "Specified"; T.ckwd "("; pparg v; T.ckwd ")"]
    | "Core.Vunpecified", [_ (*ty*)] -> Core, Some [T.ckwd "Unspecified"(*; T.ckwd "("; pparg ty; T.ckwd ")"*)]
         (* TODO: not sure it's really a good idea to suppress the ty's *)
    | "Core.Vunit", [] -> Core, Some [T.ckwd "Unit"]
    | "Core.Vtrue", [] -> Core, Some [T.ckwd "True"]
    | "Core.Vfalse", [] -> Core, Some [T.ckwd "False"]
    | "Core.Vctype", [ctype] -> Core, Some [pparg ctype]
    | "Core.Vlist", [cbt; vs] -> Core, Some [ core_expr_list vs (T.ckwd "[") (T.ckwd "]") (T.ckwd ";") Seplist.Optional ]
    | "Core.Vtuple", [vs] -> Core, Some [ core_expr_list vs (T.ckwd "(") (T.ckwd ")") (T.ckwd ",") Seplist.Optional ]

    (** Core.generic_ctor *)
    | "Core.Cnil", [ty] -> Core, Some [T.ckwd "Nil"]
    | "Core.Ccons", [] -> Core, Some [T.ckwd "Cons"]
    | "Core.Ctuple", [] -> Core, Some [T.ckwd "Tuple"]
    | "Core.Carray", [] -> Core, Some [T.ckwd "Array"]
    | "Core.Civmax", [] -> Core, Some [T.ckwd "Ivmax"]
    | "Core.Civmin", []  -> Core, Some [T.ckwd "Ivmin"]
    | "Core.Civsizeof", [] -> Core, Some [T.ckwd "Ivsizeof"]
    | "Core.Civalignof", [] -> Core, Some [T.ckwd "Ivalignof"]
    | "Core.Cspecified", [] -> Core, Some [T.ckwd "Specified"]
    | "Core.Cunspecified", [] -> Core, Some [T.ckwd "Unspecified"]

    (** additional Core_aux.mk_ functions to construct generic_ctor applications *)
    | "Core_aux.mk_specified_pe", [e] -> Core, Some ([T.ckwd "Specified"; T.ckwd "("; pparg e; T.ckwd ")"])
    | "Core_aux.mk_unspecified_pe", [ _ (*ty*)] -> Core, Some ([T.ckwd "Unspecified"])
    (* mk_unspecified_pe actually makes a Vunspecified, not a Cunspecified...? *)
    | "Core_aux.mk_list_pe", [es] -> Core, Some ([core_expr_list es (T.ckwd "[") (T.ckwd "]") (T.ckwd ";") Seplist.Optional])
    | "Core_aux.mk_tuple_pe", [es] -> Core, Some ([core_expr_list es (T.ckwd "(") (T.ckwd ")") (T.ckwd ",") Seplist.Optional])
    | "Core_aux.mk_ivmax_pe", [ty] -> Core, Some [T.ckwd "ivmax"; T.ckwd "("; pparg ty; T.ckwd ")"]
    | "Core_aux.mk_ivmin_pe", [ty] -> Core, Some [T.ckwd "ivmin"; T.ckwd "("; pparg ty; T.ckwd ")"]
    | "Core_aux.mk_ivsizeof_pe", [ty] -> Core, Some [T.ckwd "ivsizeof"; T.ckwd "("; pparg ty; T.ckwd ")"]
    | "Core_aux.mk_ivalignof_pe", [ty] -> Core, Some [T.ckwd "ivalignof"; T.ckwd "("; pparg ty; T.ckwd ")"]

    (** Core.maybesym *)
    (* TODO: this needs special-casing as it uses the Lem maybe type - would be better to use a distinguished Core type *)


    (** Core.generic_pattern *)
(* TODO    | "Core.CaseBase", [maybesym (* : Nothing | Just tyvarsym*) ] -> Core,*)
    | "Core.CaseCtor", [ctor; pats] -> Core, Some ([pparg ctor; core_expr_list pats (T.ckwd "(") (T.ckwd ")") (T.ckwd ",") Seplist.Optional])

    (** Core_aux mk_ functions to construct Core patterns *)
    (* these special-case the pp for tuples and specified patterns, but leave the Core.generic_pattern using the uniform construction *)
    | "Core_aux.mk_empty_pat", [] -> Core, Some ([T.ckwd "_"])
    | "Core_aux.mk_sym_pat", [sym; _ (*bTy*)] -> Core, Some [pparg sym]
    | "Core_aux.mk_tuple_pat", [pats] -> Core, Some ([core_expr_list pats (T.ckwd "(") (T.ckwd ")") (T.ckwd ",") Seplist.Optional])
    | "Core_aux.mk_specified_pat", [pat] -> Core, Some ([T.ckwd "Specified"; T.ckwd "("; pparg pat; T.ckwd ")"])

      (** Core.pexpr_ *) (** following core.ott *)
    | "Core.PEsym", [sym] | "Core_aux.mk_sym_pe", [_(*ty*); sym] -> Core, Some [pparg sym]
    | "Core.PEimpl", [iCst] -> Core, Some [pparg iCst]

    | "Core.PEval", [v] -> Core, Some [pparg v]
    | "Core_aux.mk_integer_pe", [v] -> Core, (*Some [pparg v]*)
          Some ([meta "{\\color{blue}"; pparg v ; meta "}" ])   (* TODO: this hack won't work for html *)

    | "Core.PEundef", [ub] | "Core_aux.mk_undef_pe", [ub] -> Core, Some [T.ckwd "undef"; T.ckwd "("; pparg ub; T.ckwd ")"]
    | "Core.PEerror", [s; e] | "Core_aux.mk_error_pe", [s;e] -> Core, Some  [T.ckwd "error"; T.ckwd "("; pparg s; T.ckwd ","; pparg e; T.ckwd ")"]


    | "Core.PEctor", [ctor; pes] -> Core, Some ([pparg ctor; pparg pes]) (*core_expr_list pes (T.ckwd "(") (T.ckwd ")") (T.ckwd ",") Seplist.Optional])*)

    | "Core.PEcase", [e1; clauses] -> Core, Some ([T.ckwd "case"; space; pparg e1; space; T.ckwd "with"] @ (core_clause_list clauses))


    | "Core.PEarray_shift", [e1; ty; e2] | "Core_aux.mk_array_shift", [e1; ty; e2] -> Core, Some [T.ckwd "array_shift"; T.ckwd "("; pparg e1; T.ckwd ","; pparg ty; T.ckwd ","; pparg e2; T.ckwd ")"]
    | "Core.PEmember_shift", [e1; sym; id] (*| "Core_aux.mk_member_shift", [e1; sym; id]*) -> Core, Some [T.ckwd "member_shift"; T.ckwd "("; pparg e1; T.ckwd ","; pparg sym; T.ckwd "."; pparg id; T.ckwd ")"]

    | "Core.PEnot", [e] | "Core_aux.mk_not_pe", [e] -> Core, Some [T.ckwd "not"; T.ckwd "("; pparg e; T.ckwd ")"]
    | "Core.PEop", [op; pe1; pe2] | "Core_aux.mk_op_pe", [op; pe1; pe2] -> Core, Some [pparg pe1; space; ppc_deconstruct op; space; pparg pe2]

    | "Core.PEstruct", [tag; struct_members] -> Core, Some [T.ckwd "("; T.ckwd "struct"; pparg tag; T.ckwd ")"; core_struct_member_list struct_members]

    | "Core.PEunion", [tag; id; pe] -> Core, Some [T.ckwd "("; T.ckwd "union"; pparg tag; T.ckwd ")"; T.ckwd "{"; T.ckwd "."; pparg id; T.ckwd "="; pparg pe; T.ckwd "}"]


    | "Core.PEcall", [nm; pes] -> Core, Some ([pparg nm; core_expr_list pes (T.ckwd "(") (T.ckwd ")") (T.ckwd ",") Seplist.Optional])
    | "Core.PElet", [pat; pe1; pe2] | "Core_aux.mk_let_pe", [pat; pe1; pe2] -> Core, Some [T.ckwd "let" ; pparg pat ; T.ckwd "="; pparg pe1; space; T.ckwd "in"; space; pparg pe2 ]
    | "Core.PEif", [pe1; pe2; pe3] | "Core_aux.mk_if_pe", [pe1; pe2; pe3] -> Core, Some  [T.ckwd "if" ; pparg pe1; space; T.ckwd "then"; pparg pe2; space; T.ckwd "else"; space; pparg pe3 ]

    | "Core.PEis_scalar", [e] -> Core, Some [T.ckwd "is_scalar"; T.ckwd "("; pparg e; T.ckwd ")"]
    | "Core.PEis_integer", [e] -> Core, Some [T.ckwd "is_integer"; T.ckwd "("; pparg e; T.ckwd ")"]
    | "Core.PEis_signed", [e] -> Core, Some [T.ckwd "is_signed"; T.ckwd "("; pparg e; T.ckwd ")"]
    | "Core.PEis_unsigned", [e] -> Core, Some [T.ckwd "is_unsigned"; T.ckwd "("; pparg e; T.ckwd ")"]


    (** generic_pexpr *)
    | "Core.Pexpr", [ty; pe] -> Core, Some [pparg pe]

    (** Mem_memop *)
    | "Core.PtrEqNe", [peo] -> Core, Some [pparg peo]
    | "Core.PtrRel", [pro] -> Core, Some [pparg pro]
    | "Core.Ptrdiff", [] -> Core, Some [T.ckwd "ptrdiff"]
    | "Core.IntFromPtr", [] -> Core, Some [T.ckwd "intFromPtr"]
    | "Core.PtrFromInt", [] -> Core, Some [T.ckwd "ptrFromInt"]
    | "Core.PtrValidForDeref", [] -> Core, Some [T.ckwd "ptrValidForDeref"]

    (** generic_expr *)
    (* | pure ( generic_pexpr ) :: :: pure  {{ com  pure expression }} *)
    | "Core.Epure", [pexpr] -> Core, Some [T.ckwd "pure" ; T.ckwd "("; pparg pexpr; T.ckwd ")"]

    (* | ptrop ( Mem_memop , generic_pexpr1 , .. , generic_pexprn ) :: :: memop {{ com pointer op involving memory }} *)
    | "Core.Ememop", [memop; pes] -> Core, Some ([pparg memop; T.ckwd "("; core_expr_list pes emp emp (T.ckwd ",") Seplist.Optional; T.ckwd ")"])

    (* | generic_paction  :: :: action {{ com memory action }} *)
    | "Core.Eaction", [a] -> Core, Some [pparg a]

    (* | case generic_pexpr with </ | generic_patterni => generic_expri // i /> end :: :: case {{ com pattern matching }} *)
    | "Core.Ecase", [e1; clauses] -> Core, Some ([T.ckwd "case"; space; pparg e1; space; T.ckwd "with"] @ (core_clause_list clauses))

    (* | let generic_pattern = generic_pexpr in generic_expr :: :: let (+ bind b(generic_pattern) in generic_expr +) {{ com Core let  }} *)
    | "Core.Elet", [pat; e1; e2] -> Core, Some [T.ckwd "let" ; pparg pat ; T.ckwd "="; pparg e1; space; T.ckwd "in"; space; pparg e2 ]
    (* | if generic_pexpr then generic_expr1 else generic_expr2 :: :: if {{ com Core if  }} *)
    | "Core.Eif", [e1; e2; e3] -> Core, Some  [T.ckwd "if" ; pparg e1; space; T.ckwd "then"; pparg e2; space; T.ckwd "else"; space; pparg e3 ]
    (* | skip :: :: skip {{ com  skip }} *)
    | "Core.Eskip", [] -> Core, Some [T.ckwd "skip"]

    (* | pcall ( a  generic_pexpr , generic_pexpr1 , .. , generic_pexprn ) :: :: proc {{ com Core procedure call }} *)
    | "Core.Eproc", [_ (*a*); nm; es] -> Core, Some ([pparg nm; core_expr_list es (T.ckwd "(") (T.ckwd ")") (T.ckwd ",") Seplist.Optional])
    (* | return ( generic_pexpr ) :: :: return {{ com Core procedure return }} *)
    | "Core.Ereturn", [e] -> Core, Some [T.ckwd "return" ; T.ckwd "("; pparg e; T.ckwd ")"]

    (* | unseq ( generic_expr1 , .. , generic_exprn ) :: :: unseq {{ com unsequenced expressions }} *)
    | "Core.Eunseq", [es] | "Core_aux.mk_unseq", [es] -> Core, Some ([T.ckwd "unseq"; core_expr_list es (T.ckwd "(") (T.ckwd ")") (T.ckwd ",") Seplist.Optional])
   (* | let weak generic_pattern = generic_expr1 in generic_expr2 :: :: wseq {{ com weak sequencing }} *)
    | "Core.Ewseq", [pat; e1; e2] -> Core, Some [T.ckwd "let" ; space; T.ckwd "weak"; pparg pat ; T.ckwd "="; pparg e1; space; T.ckwd "in"; space; pparg e2 ]
    (* | let strong generic_pattern = generic_expr1 in generic_expr2 :: :: sseq {{ com strong sequencing }} *)
    | "Core.Esseq", [pat; e1; e2] -> Core, Some [T.ckwd "let" ; space; T.ckwd "strong"; pparg pat ; T.ckwd "="; pparg e1; space; T.ckwd "in"; space; pparg e2 ]
    (* | let atomic maybe_Symbol_sym_core_base_type = generic_action1 in generic_paction2 :: :: aseq  {{ com atomic sequencing }}% (\* this ctor doesn't exist at runtine *\) *)
    | "Core.Easeq", [sym; a1; a2] -> Core, Some [T.ckwd "let" ; space; T.ckwd "atomic"; pparg sym ; T.ckwd "="; pparg a1; space; T.ckwd "in"; space; pparg a2 ]
    (* | indet [ nat ] ( generic_expr ) :: :: indet  {{ com indeterminately sequenced expr }} % (\* this ctor doesn't exist at runtine *\) *)
    | "Core.Eindet", [n; e] -> Core, Some [T.ckwd "indet"; T.ckwd "["; pparg n; T.ckwd "]"; T.ckwd "("; pparg e; T.ckwd ")"]

    (* | bound [ nat ] ( generic_expr ) :: :: bound  {{ com $\ldots$and boundary }} %(\* this ctor doesn't exist at runtine *\) *)
    | "Core.Ebound", [n; e] -> Core, Some [T.ckwd "bound"; T.ckwd "["; pparg n; T.ckwd "]"; T.ckwd "("; pparg e; T.ckwd ")"]

    (* | nd ( generic_expr1 , .. , generic_exprn ) :: ::  nd {{ com nondeterministic sequencing }} *)
    | "Core.End", [es] -> Core, Some ([T.ckwd "nd"; core_expr_list es (T.ckwd "(") (T.ckwd ")") (T.ckwd ",") Seplist.Optional])

    (* | save label ( </ Symbol_symi : ctypei // , // i /> ) in generic_expr :: :: save  {{ com save label }} *)
    | "Core.Esave", (label::_) -> Core, Some [T.ckwd "save"; space; pparg label]  (* TODO: fix wrt changes to save/run *)

    (* | run a label ( </ Symbol_symi := generic_pexpri // , // i /> ) :: :: run  {{ com run from label }} *)
    | "Core.Erun", (label::_) -> Core, Some [T.ckwd "run"; space; pparg label]

    (* | par ( generic_expr1 , .. , generic_exprn ) :: :: par  {{ com cppmem thread creation }}%(\* Parallel composition: for cppmem-style composition *\) *)
    | "Core.Epar", [es] -> Core, Some ([T.ckwd "par"; core_expr_list es (T.ckwd "(") (T.ckwd ")") (T.ckwd ",") Seplist.Optional])

    (* | wait ( Thread_thread_id ) ::  :: wait  %(\* TODO: this will need to have a Core type annotation to allow typecheck ... *\) *)
    | "Core.Ewait", [tid] -> Core, Some [T.ckwd "wait"; T.ckwd "("; pparg tid; T.ckwd ")"]

    (* TODO *)
    (* | Eloc Loc_t generic_expr :: X :: loc  *)


    (** generic_actionB *)
    | "Core.Create", [pe1; pe2; symprefix] -> Core, Some [T.ckwd "create"; T.ckwd "("; pparg pe1; T.ckwd ","; pparg pe2; space; pparg symprefix; T.ckwd ")"]
    | "Core.Alloc", [pe1; pe2; symprefix] -> Core, Some [T.ckwd "alloc"; T.ckwd "("; pparg pe1; T.ckwd ","; pparg pe2; space; pparg symprefix; T.ckwd ")"]
    | "Core.Kill", [pe] -> Core, Some [T.ckwd "kill"; T.ckwd "("; pparg pe; T.ckwd ")"]
    | "Core.Store", [pe1; pe2; pe; mo] -> Core, Some [T.ckwd "store"; T.ckwd "("; pparg pe1; T.ckwd ","; pparg pe2; T.ckwd ","; pparg pe; T.ckwd ","; pparg mo;  T.ckwd ")"]
    | "Core.Load", [pe1; pe2; mo] -> Core, Some [T.ckwd "load"; T.ckwd "("; pparg pe1; T.ckwd ","; pparg pe2; T.ckwd ","; pparg mo;  T.ckwd ")"]
    | "Core.RMW", [pe1; pe2; pe3; pe4; mo1; mo2] -> Core, Some [T.ckwd "rmw"; T.ckwd "("; pparg pe1; T.ckwd ","; pparg pe2; T.ckwd ","; pparg pe3; T.ckwd ","; pparg pe4; T.ckwd ","; pparg mo1; T.ckwd ","; pparg mo2;  T.ckwd ")"]
    | "Core.Fence", [pe] -> Core, Some [T.ckwd "fence"; T.ckwd "("; pparg pe; T.ckwd ")"]

    (** generic_action *)
    | "Core.Action", [l; a; ga] -> Core, Some [T.ckwd "action"; space; pparg ga]  (* TODO: suppressing both l and a; is that right?  And maybe the concrete syntax for Core should be harmonised to have parens for all these kinds of thing...*)

    (** generic_paction *)
    | "Core.Paction", [pol; ga] -> Core, Some [T.ckwd "Paction"; space; pparg pol; space; pparg ga]

    (** Core operators *)
    | "Core.OpAdd", [] -> Core, Some ([T.ckwd "+"  ])
    | "Core.OpSub", [] -> Core, Some ([T.ckwd "-"  ])
    | "Core.OpMul", [] -> Core, Some ([T.ckwd "*"  ])
    | "Core.OpDiv", [] -> Core, Some ([T.ckwd "/"  ])
    | "Core.OpMod", [] -> Core, Some ([T.ckwd "%"  ])
    | "Core.OpExp", [] -> Core, Some ([T.ckwd "^"  ])
    | "Core.OpEq" , [] -> Core, Some ([T.ckwd "="  ])
    | "Core.OpGt" , [] -> Core, Some ([T.ckwd ">"  ])
    | "Core.OpLt" , [] -> Core, Some ([T.ckwd "<"  ])
    | "Core.OpGe" , [] -> Core, Some ([T.ckwd ">=" ])
    | "Core.OpLe" , [] -> Core, Some ([T.ckwd "<=" ])
    | "Core.OpAnd", [] -> Core, Some ([T.ckwd "/\\"])
    | "Core.OpOr" , [] -> Core, Some ([T.ckwd "\\/"])



(* for debugging, announce the Lem-internal Core identifier *)
(*
    | s,_ when String.sub s 0 5 = "Core." -> Core, Some ([meta "{\\color{red}[\\!["; meta c_id_string ; meta "]\\!]}" ]
(*  @ B.function_application_to_output (exp_to_locn e) trans false e cd args (use_ascii_rep_for_const cd)*))
*)

(** AilSyntax.statement *)
    | "AilSyntax.AilSskip", [] -> Ail, Some  [T.akwd "skip" ]
    | "AilSyntax.AilSexpr", [e1] -> Ail, Some  [pparg e1; ]
    | "AilSyntax.AilSblock", [b; ss] -> Ail, Some  [T.akwd "{"; space; pparg b; space; pparg ss; space; T.akwd "}"]
    | "AilSyntax.AilSif", [e1; s1; s2] -> Ail, Some  [T.akwd "if" ; pparg_flip_lskip_string "(" e1; T.akwd ")"; space; pparg s1; space; T.akwd "else"; space; pparg s2 ]
    | "AilSyntax.AilSwhile", [e1; s1] -> Ail, Some  [T.akwd "while" ; pparg_flip_lskip_string "(" e1; T.akwd ")"; space; pparg s1  ]
    | "AilSyntax.AilSdo", [s1; e1] -> Ail, Some  [T.akwd "do" ; space; pparg s1; space; T.akwd "while"; pparg_flip_lskip_string "(" e1; T.akwd ")"; ]
    | "AilSyntax.AilSbreak", [] -> Ail, Some  [T.akwd "break" ]
    | "AilSyntax.AilScontinue", [] -> Ail, Some  [T.akwd "continue" ]
    | "AilSyntax.AilSreturnVoid", [] -> Ail, Some  [T.akwd "returnVoid" ]


    | "AilSyntax.AilSreturn", [e1] -> Ail, Some  [T.akwd "return" ; space; pparg e1; ]
    | "AilSyntax.AilSswitch", [e1; s1] -> Ail, Some  [T.akwd "switch" ; pparg_flip_lskip_string "(" e1; T.akwd ")"; space; pparg s1  ]
    | "AilSyntax.AilScase", [iCst; s1] -> Ail, Some  [T.akwd "case" ; space; pparg iCst; T.akwd ":"; pparg s1; ]
    | "AilSyntax.AilSdefault", [s1] -> Ail, Some  [T.akwd "default" ; space; T.akwd ":"; pparg s1; ]
    | "AilSyntax.AilSlabel", [id; s1] -> Ail, Some  [pparg id ; space; T.akwd ":"; space; pparg s1; ]
    | "AilSyntax.AilSgoto", [id] -> Ail, Some  [T.akwd "goto"; space; pparg id ]
    | "AilSyntax.AilSdeclaration", [ds] -> Ail, Some  [T.akwd "declaration-TODO"; space; pparg ds ]
    | "AilSyntax.AilSpar", [ss] -> Ail, Some  [T.akwd "par-TODO"; space; pparg ss ]
(** AilSyntax.expression *)
    | "AilSyntax.AilEunary", [op;e] ->
        begin
          match deconstruct_arg op with
          | Some (c_id_string',[]) ->
              begin
                match ppc (c_id_string',[]),  ail_unary_is_postfix c_id_string' with
                | (kind,(Some op_output)), true  -> Ail, Some  [pparg e; (concat emp op_output) ]
                | (kind,(Some op_output)), false -> Ail, Some  [pparg_flip_lskip (concat emp op_output) e ]
                | (kind,None), true -> Ail, Some [pparg op; pparg e;]
              end
          | None -> Ail, Some [pparg op; pparg e;]
        end
    | "AilSyntax.AilEbinary", [e1;op;e2] ->
        Ail, Some [
        pparg e1;
        (match deconstruct_arg op with
        | Some (c_id_string',xs) ->
            begin
              match ppc (c_id_string',xs) with
              | kind, Some output -> concat emp output
              | kind, None -> pparg op
            end
        | None ->
            pparg op);
        pparg e2]
    | "AilSyntax.AilEassign", [e1;e2] -> Ail, Some  [pparg e1; space; T.akwd "="; space; pparg e2; ]
    | "AilSyntax.AilEcompoundAssign", [e1;aop;e2] -> Ail, Some  [pparg e1; space; pparg aop; T.akwd "="; space; pparg e2; ]
    | "AilSyntax.AilEcond", [e1;e2;e3] -> Ail, Some  [pparg e1; space; T.akwd "?"; space; pparg e2; space; T.akwd ":"; space; pparg e3; ]
    | "AilSyntax.AilEcast", [q; ct; e1] -> Ail, Some  [ pparg_flip_lskip_string "(" q; space; pparg ct; space; T.akwd ")"; space; pparg e1; ]
    | "AilSyntax.AilEcall", [e1; es] -> Ail, Some  [pparg e1; pparg_flip_lskip_string "(" es; T.akwd ")"; space; ]
          (* now the grammar and lem diverge, so I'll stop for now*)

          (* for debugging, announce the Lem-internal AilSyntax identifier *)
    | s,_ when String.length s >=13 && String.sub s 0 13 = "AilSyntax.Ail" ->
        Ail, Some ([meta "{\\color{red}[\\!["; meta c_id_string ; meta "]\\!]}" ]
              (*@let oL = B.pattern_application_to_output p.locn (pat print_backend) cd ps (use_ascii_rep_for_const cd) in
              oL*))
(** AilSyntax binary operators *)
    | "AilSyntax.Arithmetic", [p] ->
        begin
          match deconstruct_arg p with
          | Some (c_id_string', []) ->
              begin
                match c_id_string' with
                | "AilSyntax.Mul"  -> Ail, Some ([T.akwd "*" ])
                | "AilSyntax.Div"  -> Ail, Some ([T.akwd "/" ])
                | "AilSyntax.Mod"  -> Ail, Some ([T.akwd "%" ])
                | "AilSyntax.Add"  -> Ail, Some ([T.akwd "+" ])
                | "AilSyntax.Sub"  -> Ail, Some ([T.akwd "-" ])
                | "AilSyntax.Shl"  -> Ail, Some ([T.akwd "<<"])
                | "AilSyntax.Shr"  -> Ail, Some ([T.akwd ">>"])
                | "AilSyntax.Band" -> Ail, Some ([T.akwd "&" ])
                | "AilSyntax.Bor"  -> Ail, Some ([T.akwd "|" ])
                | "AilSyntax.Bxor" -> Ail, Some ([T.akwd "^" ])
                | _ -> Ail, None
              end
          | _ -> Ail, None
        end
(* repeating the above not inside an AilSyntax.Arithmetic *)
    | "AilSyntax.Mul" ,[] -> Ail, Some ([T.akwd "*" ])
    | "AilSyntax.Div" ,[] -> Ail, Some ([T.akwd "/" ])
    | "AilSyntax.Mod" ,[] -> Ail, Some ([T.akwd "%" ])
    | "AilSyntax.Add" ,[] -> Ail, Some ([T.akwd "+" ])
    | "AilSyntax.Sub" ,[] -> Ail, Some ([T.akwd "-" ])
    | "AilSyntax.Shl" ,[] -> Ail, Some ([T.akwd "<<"])
    | "AilSyntax.Shr" ,[] -> Ail, Some ([T.akwd ">>"])
    | "AilSyntax.Band",[] -> Ail, Some ([T.akwd "&" ])
    | "AilSyntax.Bor" ,[] -> Ail, Some ([T.akwd "|" ])
    | "AilSyntax.Bxor",[] -> Ail, Some ([T.akwd "^" ])


    | "AilSyntax.Comma",[] -> Ail, Some ([T.akwd "," ])
    | "AilSyntax.And",[]   -> Ail, Some ([T.akwd "&&"])
    | "AilSyntax.Or",[]    -> Ail, Some ([T.akwd "||"])
    | "AilSyntax.Lt",[]    -> Ail, Some ([T.akwd "<" ])
    | "AilSyntax.Gt",[]    -> Ail, Some ([T.akwd ">" ])
    | "AilSyntax.Le",[]    -> Ail, Some ([T.akwd "<="])
    | "AilSyntax.Ge",[]    -> Ail, Some ([T.akwd ">="])
    | "AilSyntax.Eq",[]    -> Ail, Some ([T.akwd "=="])
    | "AilSyntax.Ne",[]    -> Ail, Some ([T.akwd "!="])

(** AilSyntax unary operators *)
    | "AilSyntax.Plus"       ,[] -> Ail, Some ([T.akwd "+"])
    | "AilSyntax.Minus"      ,[] -> Ail, Some ([T.akwd "-"])
    | "AilSyntax.Bnot"       ,[] -> Ail, Some ([T.akwd "!"])
    | "AilSyntax.Address"    ,[] -> Ail, Some ([T.akwd "&"])
    | "AilSyntax.Indirection",[] -> Ail, Some ([T.akwd "*"])
    | "AilSyntax.PostfixIncr",[] -> Ail, Some ([T.akwd "++"])  (*postfix*)
    | "AilSyntax.PostfixDecr",[] -> Ail, Some ([T.akwd "--"])  (*postfix*)





    | _ -> Plain, None

  in
  ppc (c_id_string,args)


let rec pat print_backend p = match p.term with
  | P_wild(s) ->
      ws s ^
      T.pat_wildcard

  | P_as(s1,p,s2,(n,l),s3) ->
      ws s1 ^
      kwd "(" ^
      pat print_backend p ^
      ws s2 ^
      T.pat_as ^
      Name.to_output Term_var n ^
      ws s3 ^
      kwd ")"

  | P_typ(s1,p,s2,t,s3) ->
      ws s1 ^
      kwd "(" ^
      pat print_backend p ^
      ws s2 ^
      T.typ_sep ^
      typ print_backend t ^
      ws s3 ^
      kwd ")"
  | P_var(n) ->
      Name.to_output Term_var n
  | P_const(cd,ps) ->
      begin
        match cerberus_pat print_backend p cd ps with
        | kind, Some output ->
            let lskip = Typed_ast.ident_get_lskip cd in
(*            concat texspace(*?*) (ws lskip :: [T.asbr output] )*)
(*            ws lskip ^ (T.asbr kind (concat texspace output))*)
            ws lskip ^ (concat texspace output)
        | _, None ->
            let oL = B.pattern_application_to_output p.locn (pat print_backend) cd ps (use_ascii_rep_for_const cd) in
            concat texspace oL
      end
  | P_backend(sk,i,_,ps) ->
      backend print_backend sk i ^
      concat texspace (List.map (pat print_backend) ps)
  | P_record(s1,fields,s2) ->
      ws s1 ^
      T.pat_rec_start ^
      flat (Seplist.to_sep_list (patfield print_backend) (sep T.rec_sep) fields) ^
      ws s2 ^
      T.pat_rec_end

  | P_tup(s1,ps,s2) ->
      ws s1 ^
      kwd "(" ^
      flat (Seplist.to_sep_list (pat print_backend) (sep T.tup_sep) ps) ^
      ws s2 ^
      kwd ")"

  | P_list(s1,ps,s2) ->
      ws s1 ^
      T.list_begin ^
      flat
        (Seplist.to_sep_list_last T.last_list_sep
           (pat print_backend) (sep T.list_sep) ps) ^
      ws s2 ^
      T.list_end

  | P_vector(s1,ps,s2) ->
      ws s1 ^
      T.vector_begin ^
      flat
        (Seplist.to_sep_list_last Seplist.Optional (pat print_backend) (sep (kwd ";")) ps) ^
      ws s2 ^
      T.vector_end

  | P_vectorC(s1,ps,s2) ->
      ws s1 ^
      kwd "[|" ^
      flat (List.map (pat print_backend) ps) ^
      ws s2 ^
      kwd "|]"

  | P_paren(s1,p,s2) ->
      ws s1 ^
      kwd "(" ^
      pat print_backend p ^
      ws s2 ^
      kwd ")"

  | P_cons(p1,s,p2) ->
      pat print_backend p1 ^
      ws s ^
      T.cons_op ^
      pat print_backend p2

  | P_num_add ((n, _),s1,s2,i) ->
      T.pat_add_op ((Name.to_output Term_var n)) s1 s2 i
  | P_lit(l) ->
      lit l true (annot_to_typ p)

  | P_var_annot(n,t) ->
      kwd "(" ^
      Name.to_output Term_var n ^
      T.typ_sep ^
      typ print_backend t ^
      kwd ")"

and patfield print_backend (fd,s1,p) =
  field_ident_to_output fd ^
  ws s1 ^
  kwd "=" ^
  pat print_backend p

and patlist print_backend ps =
  match ps with
  | [] -> emp
  | [p] -> pat print_backend p
  | p::((_::_) as ps') -> pat print_backend p ^ texspace ^ patlist print_backend ps'

and cerberus_pat print_backend p cd ps =
  match !Backend_common.cerberus_pp, T.target with
  | true, Target_no_ident (Target_tex|Target_html) ->
    let pppat p' = pat print_backend p' in

    let rec deconstruct_pat p =
      match p.term with
      | P_paren(s1,p',s2) -> deconstruct_pat p'  (* suppress parens in op pattern output *)
      | P_const(cd, ps) ->
          let (c_descr : Typed_ast.const_descr) = c_env_lookup Ast.Unknown A.env.c_env cd.descr in
          let (c_id_string : string) = normalise_c_id_string (Path.to_string c_descr.const_binding) in
          Some (c_id_string, ps)
      | _ -> None in


    let (c_descr : Typed_ast.const_descr) = c_env_lookup Ast.Unknown A.env.c_env cd.descr in
    (* TODO: how to pull out the initial lskips from the Constant?                  let lskip = Ident.get_lskip c_descr.const_binding.id_path in  *)
    begin
      match deconstruct_pat p with
      | Some (c_id_string,ps) ->
          ppcerberus (c_id_string,ps) deconstruct_pat pppat (pppat_flip_lskip pppat)
            (pat_core_expr_list pppat) (pat_core_expr_pattern_list pppat) (pat_core_expr_option_pattern pppat) (pat_core_clause_list pppat) (pat_core_struct_member_list pppat)
      | None -> Plain, None
    end
  | _,_ ->
      Plain,None


let rec exp print_backend e =
let is_user_exp = is_pp_exp e in
match C.exp_to_term e with
  | Var(n) ->
      Name.to_output Term_var n
  | Backend(sk, i) ->
      backend print_backend sk i
  | Nvar_e(s,n) ->
      ws s ^ id Nexpr_var (Ulib.Text.(^^^) T.nexp_var (Nvar.to_rope n))
  | Constant(cd) ->
      Output.concat emp
        (match !Backend_common.cerberus_pp, T.target with
        | true, Target_no_ident (Target_tex|Target_html) ->
            begin
              match cerberus_exp_app print_backend (exp print_backend) e e [] cd with
              | (kind, Some output) ->
                  let lskip = Typed_ast.ident_get_lskip cd in
                  ws lskip :: output
              | (_, None) ->
                  B.function_application_to_output (exp_to_locn e) (*trans*) (exp print_backend) false e cd [] (use_ascii_rep_for_const cd)
            end
        | _,_ ->
            (B.function_application_to_output (exp_to_locn e) (exp print_backend) false e cd [] (use_ascii_rep_for_const cd))
        )
  | Fun(s1,ps,s2,e) ->
      ws s1 ^
      T.fun_start ^
      T.fun_kwd ^
      patlist print_backend ps ^
      ws s2 ^
      T.fun_sep ^
      exp print_backend e ^
      T.fun_end

  | Function(s1,f,s2) ->
      ws s1 ^
      T.function_start ^
      flat (Seplist.to_sep_list
              (fun (p,s1,e,l) ->
                 pat print_backend p ^
                 ws s1 ^
                 T.fun_sep ^
                 exp print_backend e)
              (sep (kwd "|"))
              f) ^
        ws s2 ^
      T.function_end

  | App(e1,e2) ->
      let trans e = block (is_pp_exp e) 0 (exp print_backend e) in
      let sep = (texspace ^ break_hint_space 2) in
      let oL = begin
         (* try to strip all application and see whether there is a constant at the beginning *)
         let (e0, args) = strip_app_exp e in
         match C.exp_to_term e0 with
           | Constant cd ->
             (* constant, so use special formatting *)
               begin
                 (* special-case Cerberus output *)
                 match !Backend_common.cerberus_pp, T.target with
                 | true, Target_no_ident (Target_tex|Target_html) ->
                     begin
                       match cerberus_exp_app print_backend trans e e0 args cd with
                       | (kind, Some output) ->
                           let lskip = Typed_ast.ident_get_lskip cd in
                           ws lskip :: output
                       | (_, None) ->
                           B.function_application_to_output (exp_to_locn e) trans false e cd args (use_ascii_rep_for_const cd)
                     end
                 | _,_ ->
                     B.function_application_to_output (exp_to_locn e) trans false e cd args (use_ascii_rep_for_const cd)
               end
           | _ -> (* no constant, so use standard one *)
               List.map trans (e0 :: args)
      end in
      let o = Output.concat sep oL in
      block is_user_exp 0 o

  | Infix(e1,e2,e3) ->
      let trans e = block (is_pp_exp e) 0 (exp print_backend e) in
      let sep = (texspace ^ break_hint_space 2) in

      let oL = begin
         (* check, whether there is a constant in the middle *)
         match C.exp_to_term e2 with
           | Constant cd ->
             (* constant, so use special formatting *)
               (* special-case Cerberus output *)
               let (c_descr : Typed_ast.const_descr) = c_env_lookup Ast.Unknown A.env.c_env cd.descr in
               let (c_id_string : string) = Path.to_string c_descr.const_binding in
               let ppexp e = exp print_backend e in
               begin
                 match c_id_string with
                 (* rearrange >>= bind syntax *)
                 | _ when (try ">>=" = String.sub c_id_string (String.length c_id_string -3) 3 with Invalid_argument _ -> false) ->
                     let (e1',lskips1) = Typed_ast.alter_init_lskips (fun lskips1->(Typed_ast.no_lskips, lskips1)) e1 in
                     let (e3',lskips3) = Typed_ast.alter_init_lskips (fun lskips3->(Typed_ast.no_lskips, lskips3)) e3 in
                     (match C.exp_to_term e3' with
                     | Fun(s1,ps,s2,e) ->
                         [ws lskips1 ;
                          patlist print_backend ps ;
                          (*      ws s2 *)
                          space; T.bkwd ":=" ; space;
                          ppexp e1';
                          T.bkwd ";" ;
                          ppexp e]
                     | _ -> B.function_application_to_output (exp_to_locn e) trans true e cd [e1;e3] (use_ascii_rep_for_const cd))
(*[meta " BACKEND PP ERROR: Cerberus FUN MATCH FAILURE"] @ B.function_application_to_output (exp_to_locn e) trans true e cd [e1;e3] (use_ascii_rep_for_const cd))*)
                 | _ -> (* (*show real path for debugging:*)  [T.bkwd c_id_string] @*)
                     B.function_application_to_output (exp_to_locn e) trans true e cd [e1;e3] (use_ascii_rep_for_const cd)
               end
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
           (expfield print_backend) (sep T.rec_sep) fields) ^
      ws s2 ^
      T.rec_end

  | Recup(s1,e,s2,fields,s3) ->
        ws s1 ^
        T.recup_start ^
        exp print_backend e ^
        ws s2 ^
        T.recup_middle ^
        flat
          (Seplist.to_sep_list_last
             T.last_rec_sep
             (expfieldup print_backend) (sep T.rec_sep) fields) ^
        ws s3 ^
        T.recup_end
  | Field(e,s,fd) ->
      if (T.target = Target_no_ident Target_isa) then
        kwd "(" ^ T.field_access_start ^
        field_ident_to_output fd ^
        T.field_access_end ^
        exp print_backend e ^ kwd ")" ^
        ws s
      else
        exp print_backend e ^
        ws s ^
        T.field_access_start ^
        field_ident_to_output fd ^
        T.field_access_end

  | Case(b,s1,e,s2,cases,s3) ->
      block_hv is_user_exp 0 (
      ws s1 ^
      T.case_start ^
      exp print_backend e ^
      ws s2 ^
      T.case_sep1 ^
      break_hint_space 4 ^
      flat
        (Seplist.to_sep_list_first
           T.first_case_sep (case_line print_backend)
           (sep (break_hint_space 2 ^ T.case_sep2))
           cases) ^
      ws s3 ^
      break_hint_space 0 ^
      T.case_end)

  | Typed(s1,e,s2,t,s3) ->
      ws s1 ^
      kwd "(" ^
      exp print_backend e ^
      ws s2 ^
      T.typ_sep ^
      typ print_backend t ^
      ws s3 ^
      kwd ")"

  | Let(s1,bind,s2,e) ->
      block is_user_exp 0 (
      ws s1 ^
      T.let_start ^
      block is_user_exp 0 (remove_core @@ letbind print_backend bind) ^
      ws s2 ^
      T.let_in ^
      break_hint_space 0 ^
      exp print_backend e ^
      T.let_end)

  | Tup(s1,es,s2) ->
      block is_user_exp 0 (
      ws s1 ^
      kwd "(" ^
      flat (Seplist.to_sep_list (exp print_backend) (sep T.tup_sep) es) ^
      ws s2 ^
      kwd ")")
  | List(s1,es,s2) ->
      block is_user_exp 0 (
      ws s1 ^
      T.list_begin ^
      flat
        (Seplist.to_sep_list_last T.last_list_sep
           (exp print_backend) (sep T.list_sep) es) ^
      ws s2 ^
      T.list_end)
  | Vector(s1,es,s2) ->
      block is_user_exp 0 (
      ws s1 ^
      T.vector_begin ^
      flat
         (Seplist.to_sep_list_last T.last_list_sep
            (exp print_backend) (sep T.list_sep) es) ^ (* TODO KG Probably shouldn't be relying on the list sep operator here *)
      ws s2 ^
      T.vector_end)

  | VectorAcc(e,s1,n,s2) ->
      exp print_backend e ^ ws s1 ^
      kwd "." ^ kwd "[" ^ (* NOTE KG: Splitting .[ because need space in ident backend is not sophisticated enough to recognize this case *)
      nexp n ^
      ws s2 ^ kwd "]"

  | VectorSub(e,s1,n1,s2,n2,s3) ->
      exp print_backend e ^ ws s1 ^
      kwd "." ^ kwd "[" ^ (* NOTE KG: see above *)
      nexp n1 ^ ws s2 ^ kwd ".." ^
      nexp n2 ^ ws s3 ^ kwd "]"

  | Paren(s1,e,s2) ->
      block is_user_exp 0 (ws s1 ^ kwd "(" ^ block is_user_exp 0 (exp print_backend e ^ ws s2) ^ kwd ")")

  | Begin(s1,e,s2) ->
      ws s1 ^ T.begin_kwd ^ exp print_backend e ^ ws s2 ^ T.end_kwd

  | If(s1,e1,s2,e2,s3,e3) ->
      block is_user_exp 0 (
      ws s1 ^
      break_hint_cut ^
      T.cond_if ^
      block (is_pp_exp e1) 0 (exp print_backend e1) ^
      ws s2 ^
      T.cond_then ^
      break_hint_space 2 ^
      block (is_pp_exp e2) 0 (exp print_backend e2) ^
      ws s3 ^
      break_hint_space 0 ^
      T.cond_else ^
      break_hint_space 2 ^
      block (is_pp_exp e3) 0 (exp print_backend e3))

  | Lit(l) ->
      lit l false (exp_to_typ e)

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
           (exp print_backend) (sep T.set_sep) es) ^
         ws s2 ^
         T.set_end)
      ))

  | Setcomp(s1,e1,s2,e2,s3,vars) ->
      ws s1 ^
      T.set_start ^
      exp print_backend e1 ^
      ws s2 ^
      (if T.target = Target_no_ident Target_isa then
         (if (is_var_tup_exp e1 && NameSet.equal vars (nfmap_domain (C.exp_to_free e1))) then kwd "." else
          T.setcomp_sep ^
          flat (List.map (fun x -> id Term_var (Name.to_rope x)) (NameSet.elements vars)) ^
          T.setcomp_binding_middle)
       else
         T.setcomp_sep) ^
      exp print_backend e2 ^
      ws s3 ^
      T.set_end

  (* List comprehensions *)
  | Comp_binding(true,s1,e1,s2,s5,qbs,s3,e2,s4) ->
      if (T.target = Target_no_ident Target_isa) then
        let qb_fun =
          let temp =
            List.map (fun q ->
              match q with
                | Qb_var n -> Name.to_output Term_var n.term
                | Qb_restr(is_lst, s1, p, s2, e, s3) ->
                    ws s1 ^ pat print_backend p ^ ws s2 ^ kwd "<-" ^
                      exp print_backend e ^ ws s3) qbs
          in
            List.fold_right (^) (Util.intercalate (kwd ", ") temp) (kwd "")
        in
          ws s1 ^ kwd "[" ^ exp print_backend e1 ^ ws s2 ^ kwd "." ^ ws s5 ^
            qb_fun ^ ws s3 ^ kwd ", " ^ exp print_backend e2 ^ ws s4 ^ kwd "]"
      else
        ws s1 ^
        kwd "[" ^
        exp print_backend e1 ^
        ws s2 ^
        kwd "|" ^
        ws s5 ^
        T.setcomp_binding_start ^
        concat T.setcomp_binding_sep (List.map (quant_binding print_backend) qbs) ^
        ws s3 ^
        T.setcomp_binding_middle ^
        exp print_backend e2 ^
        ws s4 ^
        kwd "]"

  (* Set comprehensions *)
  | Comp_binding(false,s1,e1,s2,s5,qbs,s3,e2,s4) ->
      ws s1 ^
      T.set_start ^
      exp print_backend e1 ^
      ws s2 ^
      kwd "|" ^
      ws s5 ^
      T.setcomp_binding_start ^
      concat T.setcomp_binding_sep (List.map (quant_binding print_backend) qbs) ^
      ws s3 ^
      T.setcomp_binding_middle ^
      exp print_backend e2 ^
      ws s4 ^
      T.set_end

  (* TODO: Add an Isabelle transformation to nested Quants *)
  | Quant(q,qbs,s2,e) ->
      if (T.target = Target_no_ident Target_isa) then
        block is_user_exp 0 (
        kwd "(" ^
        flat (List.map (isa_quant print_backend q) qbs) ^
        break_hint_space 2 ^
        block (is_pp_exp e) 0 (
        ws s2 ^ exp print_backend e) ^
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
        flat (interspace (List.map (quant_binding print_backend) qbs)) ^
        ws s2 ^
        kwd "." ^
        texspace ^
        break_hint_space 2 ^
        block is_user_exp 0 (
        exp print_backend e))

  | Do(s1,m,do_lns,s2,e,s3,_) ->
      ws s1 ^
      kwd "do" ^
      Ident.to_output Module_name T.path_sep (B.module_id_to_ident m) ^
      do_lines print_backend do_lns ^
      ws s2 ^
      kwd "in" ^
      exp print_backend e ^
      ws s3 ^
      kwd "end"

and do_lines print_backend = function
  | [] -> emp
  | (Do_line(p,s1,e,s2)::lns) ->
      pat print_backend p ^
      ws s1 ^
      kwd "<-" ^
      exp print_backend e ^
      ws s2 ^
      kwd ";" ^
      do_lines print_backend lns

and quant_binding print_backend = function
  | Qb_var(n) ->
      Name.to_output Term_var n.term
  | Qb_restr(is_lst,s1,p,s2,e,s3) ->
      ws s1 ^
      T.quant_binding_start ^
      pat print_backend p ^
      ws s2 ^
      (if is_lst then T.list_quant_binding else T.set_quant_binding) ^
      exp print_backend e ^
      ws s3 ^
      T.quant_binding_end

and isa_quant print_backend q qb = match q with
  | Ast.Q_forall(s1) ->
      ws s1 ^ T.forall ^ (quant_binding print_backend qb) ^ kwd "." ^ space
  | Ast.Q_exists(s1) ->
      ws s1 ^ T.exists ^ (quant_binding print_backend qb) ^ kwd "." ^ space

and expfield print_backend (fd,s1,e,_) =
  field_ident_to_output fd ^
  ws s1 ^
  T.record_assign ^
  exp print_backend (if is_human_target T.target then e else mk_opt_paren_exp e)

and expfieldup print_backend (fd,s1,e,_) =
  field_ident_to_output fd ^
  ws s1 ^
  T.recup_assign ^
  exp print_backend (if is_human_target T.target then e else mk_opt_paren_exp e)

and case_line print_backend (p,s1,e,_) =
  pat print_backend p ^
  ws s1 ^
  T.case_line_sep ^
  block (is_pp_exp e) 2 (exp print_backend e)

and funcl_aux print_backend (n, t, ps, topt, s1, e) =
  let n' = Name.to_output Term_var (Name.replace_lskip n None) in
  ws (Name.get_lskip n) ^
  T.funcase_start ^
  (match T.target with
  | Target_no_ident Target_hol ->
     kwd "(" ^ n' ^ T.typ_sep ^ typ print_backend (C.t_to_src_t t) ^ kwd ")"
  | _ -> n') ^
  (match ps with [] -> emp | _ -> texspace) ^
  patlist print_backend ps ^
  begin
    match topt with
      | None -> emp
      | Some(s,t) ->
          ws s ^ T.typ_sep ^ typ print_backend t
  end ^
  T.def_binding ^
  let e = Typed_ast.append_lskips s1 e in
  core (exp print_backend (if is_human_target T.target then e else mk_opt_paren_exp e)) ^
  T.funcase_end

and funcl print_backend (({term = n; typ = t}, c, ps, topt, s1, e):funcl_aux) =
  funcl_aux print_backend (B.const_ref_to_name n false c, t, ps, topt, s1, e)

and letbind print_backend (lb, _) : Output.t = match lb with
  | Let_val(p,topt,s2,e) ->
      pat print_backend p ^
      begin
        match topt with
          | None -> emp
          | Some(s,t) -> ws s ^ T.typ_sep ^ typ print_backend t
      end ^
      ws s2 ^ T.def_binding ^ core (exp print_backend (if is_human_target T.target then e else mk_opt_paren_exp e))
  | Let_fun (n, ps, topt, s1, e) ->
      funcl_aux print_backend (n.term, n.typ, ps, topt, s1, e)



(* special-casing Cerberus Ail and Core syntax *)
and cerberus_exp_app print_backend trans e e0 args cd =

  let ppexp e = exp print_backend e in

  let deconstruct_exp e =
    match C.exp_to_term e with
    | Constant(cd') ->
        let (c_descr' : Typed_ast.const_descr) = c_env_lookup Ast.Unknown A.env.c_env cd'.descr in
        let (c_id_string' : string) = normalise_c_id_string (Path.to_string c_descr'.const_binding) in
        Some (c_id_string', [])
    | _ -> None (*T.ckwd " BACKEND PP FAILURE: CORE OP NOT CONSTANT " in*) in

  let (c_descr : Typed_ast.const_descr) = c_env_lookup Ast.Unknown A.env.c_env cd.descr in
  let (c_id_string : string) = normalise_c_id_string (Path.to_string c_descr.const_binding) in

  ppcerberus (c_id_string,args) deconstruct_exp ppexp (ppexp_flip_lskip ppexp)
    (exp_core_expr_list ppexp) (exp_core_expr_pattern_list ppexp) (exp_core_expr_option_pattern ppexp) (exp_core_clause_list ppexp) (exp_core_struct_member_list ppexp)




(* end hack *)



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
    if quoted_name then Name.to_output_quoted "\"" "\"" (Type_ctor (false, false)) n else Name.to_output (Type_ctor (false, false)) n
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
  let n' = Name.to_output (Type_ctor (false, false)) n in
  let tvs' = List.map (fun tn -> (match tn with | Tn_A (x, y, z) -> kwd (Ulib.Text.to_string y)
                                                | Tn_N (x, y, z) -> kwd (Ulib.Text.to_string y))) tvs in
    tdef_tctor false tvs n regexp ^ tyexp true n' tvs' texp

let range = function
  | Typed_ast.GtEq(_,n1,s,n2) -> nexp n1 ^ ws s ^ kwd ">=" ^ nexp n2
  | Typed_ast.Eq(_,n1,s,n2) -> nexp n1 ^ ws s ^ kwd "=" ^ nexp n2

let constraints = function
  | None -> emp
  | Some(Cs_list(l_c,op_s,l_r,s)) ->
      flat (Seplist.to_sep_list
              (fun (id,tv) ->
                 Ident.to_output Class_name T.path_sep id ^
                 tyvar tv)
              (sep (kwd","))
              l_c) ^
      (match op_s with
        | None -> emp
        | Some s1 -> ws s1 ^ kwd ";") ^
      flat (Seplist.to_sep_list range (sep (kwd",")) l_r) ^
      ws s ^
      T.typ_class_constraint_prefix_end


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
      typ false t ^
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
    flat (interspace (List.map (fun n ->
      match n with
        | QName n -> Name.to_output Term_var n.term
        | Name_typ (sk1, n, sk2, src_t, sk3) ->
          let name = Name.to_output Term_var n.term in
            ws sk1 ^ name ^ ws sk2 ^ typ false src_t ^ ws sk3) qnames)) ^
    ws s2 ^
    kwd "."
  ) else emp) ^
  (match e_opt with None -> ws s3 | Some e ->
     exp false (if T.reln_clause_add_paren then Typed_ast_syntax.mk_opt_paren_exp e else e) ^
     ws s3 ^ T.reln_clause_sep) ^
  Name.to_output Term_var (B.const_ref_to_name rname.term false rname_ref) ^
  flat (interspace (List.map (exp false) es)) ^
  T.reln_clause_end

let targets_opt = function
  | Targets_opt_none -> emp
  | Targets_opt_concrete (s1, targets, s2) ->
      ws s1 ^
      T.targets_opt_start ^
      flat (Seplist.to_sep_list target_to_output (sep T.set_sep) targets) ^
      ws s2 ^
      T.targets_opt_end
  | Targets_opt_neg_concrete (s1, targets, s2) ->
      ws s1 ^
      T.targets_opt_start_neg ^
      flat (Seplist.to_sep_list target_to_output (sep T.set_sep) targets) ^
      ws s2 ^
      T.targets_opt_end
  | Targets_opt_non_exec (s1) ->
      ws s1 ^ kwd "non_exec"

let in_target targs = Typed_ast.in_targets_opt T.target targs


(****** Isabelle ******)

let isa_op_typ texp = match texp.term with
  | Typ_fn(_,_,_) -> kwd "(" ^ typ false texp ^ kwd ")" ^ texspace
  | _ -> typ false texp


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
  name ^ kwd " " ^ T.typ_sep ^ kwd " \\<open>" ^
  flat (List.map (function x -> isa_op_typ (C.t_to_src_t x) ^ T.typ_fun_sep) ptyps) ^
  typ false (C.t_to_src_t etyp) ^
  kwd "\\<close> " ^ ws s

(*
  flat (List.map (function x -> (isa_op_typ (C.t_to_src_t x.typ) ^
  if es=[] then emp else T.typ_fun_sep)) ps) ^
  flat (List.map (function ex -> typ (C.t_to_src_t (exp_to_typ ex))) es) ^
*)

let isa_is_simple_funcl_aux ((_, _, ps, _, _, _):funcl_aux) : bool =
   List.for_all (fun p -> (Pattern_syntax.is_var_wild_pat p)) ps

let isa_funcl_header (({term = n}, c, ps, topt, s1, (e : Typed_ast.exp)):funcl_aux) =
  isa_mk_typed_def_header (Name.to_output Term_var (B.const_ref_to_name n true c), List.map Types.annot_to_typ ps, s1, exp_to_typ e)

let isa_funcl_header_seplist clause_sl =
  let clauseL = Seplist.to_list clause_sl in
  let (_, clauseL_filter) = List.fold_left (fun (ns, acc) (({term = n'}, n'_ref, _, _, _, _) as c) ->
     let n = Name.strip_lskip (B.const_ref_to_name n' true n'_ref) in if NameSet.mem n ns then (ns, acc) else (NameSet.add n ns, c :: acc)) (NameSet.empty, []) clauseL in

  let headerL = List.map isa_funcl_header clauseL_filter in
  (Output.concat (kwd "\n                   and") headerL) ^ (kwd "where \n    ")


let isa_funcl_header_indrel_seplist clause_sl =
  let clauseL = Seplist.to_list clause_sl in
  let (_, clauseL_filter) = List.fold_left (fun (ns, acc) (Rule(_,_, _, _, _, _, _, rname, c, _),_) ->
      let n = Name.strip_lskip rname.term in
      if NameSet.mem n ns then (ns, acc) else (NameSet.add n ns, rname :: acc)) (NameSet.empty, []) clauseL in
  let headerL = List.map (fun rname ->
        isa_mk_typed_def_header(Name.to_output Term_var rname.term,[], None,
                Types.annot_to_typ rname)) clauseL_filter in
  (Output.concat (kwd "\n      and") headerL) ^ (kwd "where")


let isa_funcl_default eqsign (({term = n}, c, ps, topt, s1, (e : Typed_ast.exp)):funcl_aux) =
  kwd "\\<open>" ^ Name.to_output Term_var (B.const_ref_to_name n true c) ^ flat (List.map (pat false) ps)^ ws s1 ^ eqsign ^ kwd "(" ^ exp false e ^ kwd ")\\<close>" ^
  (let add_decl decls n t = (Name.to_output_quoted "\"" "\"" Term_var (Name.add_lskip n) ^ kwd " :: \"" ^ typ false (C.t_to_src_t t) ^ kwd "\"") :: decls in
   let decls = List.concat (List.map (fun p -> Nfmap.fold add_decl [] p.rest.pvars) ps) in
   if decls = [] then emp else kwd "\n  for " ^ Output.concat (kwd "\n  and ") decls)

let isa_funcl_abs eqsign (({term = n}, c, ps, topt, s1, (e : Typed_ast.exp)):funcl_aux) =
  kwd "\\<open>" ^ Name.to_output Term_var (B.const_ref_to_name n true c) ^ ws s1 ^ eqsign ^ kwd "(%" ^ flat (List.map (pat false) ps) ^ kwd ". " ^ exp false e ^ kwd ")\\<close>"

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

(* Isabelle requires record and datatype definitions using a typeclass parameter
   to be marked as overloaded.  In particular, definitions that are parametric
   in a machine word size need them.  This function is used to check whether
   a type definition needs them. *)
let rec is_type_with_sort t =
  match t.term with
  | Typ_wild _ | Typ_var _ | Typ_len _ -> false
  | Typ_fn (t1, _, t2) -> is_type_with_sort t1 || is_type_with_sort t2
  | Typ_tup ts -> Seplist.exists is_type_with_sort ts
  | Typ_app (p, ts) -> List.exists is_type_with_sort (B.type_app_further_types p ts)
  | Typ_backend (_, ts) -> List.exists is_type_with_sort ts
  | Typ_paren (_, t', _) -> is_type_with_sort t'
  | Typ_with_sort _ -> true

let rec isa_def_extra (gf:extra_gen_flags) d l : Output.t = match d with
  | Val_def(Fun_def(s1, s2_opt, targets, clauses))
      when gf.extra_gen_termination ->
      let (_, is_rec, try_term) = Typed_ast_syntax.try_termination_proof T.target A.env.c_env d in
      if (in_target targets && is_rec && not try_term) then
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
  | Lemma (_, lty, targets, (n, _), sk1, e) when (extra_gen_flags_gen_lty gf lty && in_target targets) -> begin
      let theorem_name = (Name.to_string (Name.strip_lskip n)) in
      let lem_st = match lty with
                     | Ast.Lemma_theorem _ -> "theorem"
                     | _ -> "lemma" in
      let solve = match lty with
                     | Ast.Lemma_assert _ -> "by ((auto; fail) | normalization)"
                     | _ -> String.concat "" ["(* Theorem: "; theorem_name; "*)(* try *) by auto"] in
      (kwd lem_st ^ space ^
      kwd theorem_name ^ ws sk1 ^ kwd ":" ^
      new_line ^
      kwd "\"" ^
      exp false e ^
      kwd "\"" ^
      new_line ^
      kwd solve ^
      new_line ^
      new_line)
    end
  | _ -> emp

let rec hol_def_extra gf d l : Output.t = match d with
  | Val_def(Fun_def(s1, s2_opt, targets, clauses))
      when gf.extra_gen_termination ->
      let (_, is_rec, try_term) = Typed_ast_syntax.try_termination_proof T.target A.env.c_env d in
      if (in_target targets && is_rec && not try_term) then
      begin
        let n =
          match Seplist.to_list clauses with
            | [] -> assert false
            | (n, c, _, _, _, _)::_ -> Name.to_string (Name.strip_lskip (B.const_ref_to_name n.term false c))
        in
        let goal_stack_setup_s = Format.sprintf "(* val gst = Defn.tgoal_no_defn (%s_def, %s_ind) *)\n" n n in
        let proof_s = Format.sprintf "val (%s_rw, %s_ind_rw) =\n  Defn.tprove_no_defn ((%s_def, %s_ind),\n    cheat (* the termination proof *)\n  )\n" n n n n in
        let store_s = Format.sprintf "val %s_rw = save_thm (\"%s_rw\", %s_rw);\nval %s_ind_rw = save_thm (\"%s_ind_rw\", %s_ind_rw);\n" n n n n n n in
        meta (String.concat "" [goal_stack_setup_s; proof_s; store_s; "\n\n"])
      end
      else emp
  | Lemma (sk0, lty, targets, (n, _), sk1, e) when (extra_gen_flags_gen_lty gf lty && in_target targets) -> begin
      let (e', _) = alter_init_lskips (fun _ -> (None, None)) e in
      match lty with
         | Ast.Lemma_assert _ -> begin
             let n_s = (Name.to_string (Name.strip_lskip n)) in
             let start = Format.sprintf "val _ = lem_assertion \"%s\" ``" n_s in
             meta start ^
             exp false e' ^
             meta "``;" ^
             new_line ^
             new_line
           end
         | _ -> begin
             let n_s = (Name.to_string (Name.strip_lskip n)) in
             let start = Format.sprintf "val %s = store_thm(\"%s\",\n" n_s n_s in
             kwd start ^
             kwd "``" ^
             exp false e' ^
             kwd "``," ^
             new_line ^
             meta (String.concat "" ["  (* Theorem: "; n_s; "*)(* your proof *) ALL_TAC"]) ^
             new_line ^
             kwd ");" ^
             new_line ^
             new_line
          end
    end
  | _ -> emp

let rec ocaml_def_extra gf d l : Output.t = match d with
  | Lemma (sk0, lty, targets, (n, _), _, e) when (extra_gen_flags_gen_lty gf lty && in_target targets) -> begin
      let is_assert = match lty with
                     | Ast.Lemma_assert _ -> true
                     | _ -> false in
      if not (is_assert) then emp else
      begin
        let n_s = Format.sprintf "\"%s\"" (String.escaped (Name.to_string (Name.strip_lskip n))) in
        let loc_s = Format.sprintf "\"%s\\n\"" (String.escaped (Reporting_basic.loc_to_string true l)) in
        let (e', _) = alter_init_lskips (fun _ -> (None, None)) e in
        meta (Format.sprintf "let _ = run_test %s %s (\n  " n_s loc_s) ^
        exp false e' ^
        meta "\n)\n\n"
      end
    end
  | _ -> emp

let def_to_label_formated_name d : (bool * string * Output.t) = begin match d with
  (* A single type abbreviation *)
  | Type_def(_, defs) ->
      begin
        match Seplist.to_list defs with
          | [((n, _),_,t_p,_,_)] ->
              (true, "Type_" ^^ Name.to_string (Name.strip_lskip n),
               Name.to_output (Type_ctor (false, false)) (B.type_path_to_name n t_p))
          | _ -> (false, "type", emp)
      end
  | (Indreln _ | Val_def _ | Val_spec _) -> begin
       let prefix = begin match d with
         | Indreln _ -> "Indrel_"
         | Val_def _ -> ""
         | Val_spec _ -> "Valspec_"
         | _ -> ""
       end in
       let ue = add_def_aux_entities Target.Target_ident true empty_used_entities d in
       match ue.used_consts with
         | [c] -> begin
             let c_name = B.const_ref_to_name (Name.add_lskip (Name.from_string "dummy")) true c in
             (true, prefix ^^ Name.to_string (Name.strip_lskip c_name),
              Name.to_output Term_field c_name)
           end
         | _ -> (false, "const", emp)
    end
  | Lemma (_, lty, _, (n, _), _, _) -> begin
      let lem_st = match lty with
                     | Ast.Lemma_theorem sk -> "theorem"
                     | Ast.Lemma_assert sk -> "assert"
                     | Ast.Lemma_lemma sk -> "lemma" in
      (true,
       String.concat "" [lem_st; "_"; Name.to_string (Name.strip_lskip n)],
       Name.to_output Term_var n)
    end
  | Module _ ->
      (false, "module", emp)
  | Rename _ ->
      (false, "rename", emp)
  | (OpenImport _ | OpenImportTarget _) ->
      (false, "open", emp)
  | Instance _ ->
      (false, "instance", emp)
  | Class _ ->
      (false, "class", emp)
  | Declaration _ ->
      (false, "declaration", emp)
  | Comment(d) ->
      (false, "comment", emp)
end

let html_source_name_def (d : def_aux) =
  let (real_label, label, _) = def_to_label_formated_name d in
  if real_label then Some (r label) else None

let html_link_def d =
  match html_source_name_def d with
  | None -> emp
  | Some s ->
      let sr = Ulib.Text.to_string s in
      kwd ( String.concat "" ["\n<a name=\"";sr;"\">"])


let val_ascii_opt = function
  | Ast.Ascii_opt_none -> emp
  | Ast.Ascii_opt_some (sk1, sk2, q, sk3) ->
     if (is_human_target T.target) then begin
       let i_escaped = match T.target with
       | Target_no_ident Target_tex -> Ident.mk_ident_strings [] (tex_escape_string q)
       | _ -> Ident.mk_ident_strings [] q in
       ws sk1 ^ kwd "[" ^ backend false sk2 i_escaped ^ ws sk3 ^ kwd "]"
     end else emp

let infix_decl = function
  | Ast.Fixity_default_assoc -> emp
  | Ast.Fixity_non_assoc (sk, n) -> ws sk ^ kwd "non_assoc" ^ num (Z.of_int n)
  | Ast.Fixity_left_assoc (sk, n) -> ws sk ^ kwd "left_assoc" ^ num (Z.of_int n)
  | Ast.Fixity_right_assoc (sk, n) -> ws sk ^ kwd "right_assoc" ^ num (Z.of_int n)


let open_import_to_output = function
  | Ast.OI_open s ->
      ws s ^ T.module_open
  | Ast.OI_include s ->
      ws s ^ T.module_include
  | Ast.OI_import s ->
      ws s ^ T.module_import
  | Ast.OI_open_import (s1, s2) ->
      ws s1 ^
      T.module_open ^
      ws s2 ^
      T.module_import
  | Ast.OI_include_import (s1, s2) ->
      ws s1 ^
      T.module_include ^
      ws s2 ^
      T.module_import

let open_import_def_to_output print_backend oi targets ms =
      if in_target targets then
        if (Target.is_human_target T.target || not (T.module_only_single_open) || List.length ms < 2) then
        begin
          	open_import_to_output oi ^
          (if Target.is_human_target T.target then
             targets_opt targets
           else
             emp) ^
          (Output.flat (List.map (fun (sk, m) ->
             ws sk ^ backend_quote_cond print_backend (id Module_name (Ulib.Text.of_string m))) ms))
        end else begin
          match ms with
            | (sk, m) :: sk_ms' -> begin
                let (oi', _) = oi_alter_init_lskips (fun _ -> (Some [Ast.Ws (r"\n")], None)) oi in
          	       open_import_to_output oi ^
                ws sk ^ backend_quote_cond print_backend (id Module_name (Ulib.Text.of_string m)) ^

               (Output.flat (List.map (fun (sk, m) ->
          	        open_import_to_output oi' ^
                  ws sk ^ backend_quote_cond print_backend (id Module_name (Ulib.Text.of_string m))) sk_ms'))
              end
            | _ -> emp (* covert by other case already *)
        end
      else emp

let rec def_internal callback (inside_module: bool) d is_user_def : Output.t = match d with
  (* A single type abbreviation *)
  | Type_def(s1, l) when is_abbrev l->
      begin
        match Seplist.hd l with
          | ((n,l),tvs,t_p,Te_abbrev(s4,t),regexp) ->
              ws s1 ^
              block is_user_def 0 (
              T.type_abbrev_start ^
              tdef_tctor T.type_abbrev_name_quoted tvs (B.type_path_to_name n t_p) regexp ^
              core (tyexp_abbrev s4 t) ^
              T.type_abbrev_end)
          | _ -> assert false
      end

  (* A single record definition *)
  | Type_def(s1, l) when is_rec l->
      begin
        match Seplist.hd l with
          | ((n,l'),tvs, t_p, Te_record(s4,s5,fields,s6),regexp) ->
              let has_sort = Seplist.exists (fun (_,_,_,t) -> is_type_with_sort t) fields in
              ws s1 ^
              block is_user_def 0 (
              T.typedefrec_start has_sort ^
              tdef_tctor false tvs (B.type_path_to_name n t_p) regexp ^
              tyexp_rec s4 s5 fields s6 ^
              T.typedefrec_end has_sort) (*
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
      let texp_variant_has_sorts = function
        | Te_variant(_, ctors) ->
          Seplist.exists (fun (_,_,_,ts) -> Seplist.exists is_type_with_sort ts) ctors
        | _ -> false
      in
      let has_sorts =
        Seplist.exists (fun (_,_,_,t,_) -> texp_variant_has_sorts t) defs
      in
        ws s ^
        block is_user_def 2 (
        T.typedef_start has_sorts ^
        flat (Seplist.to_sep_list tdef (sep (break_hint_space 0 ^ T.typedef_sep)) defs) ^
        T.typedef_end has_sorts) (*
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

  | Val_def(Let_def(s1, targets,(p, name_map, topt, sk, e))) ->
      (* TODO: use name_map to do proper renaming *)
      if in_target targets then
        ws s1 ^
        T.def_start ^
        (if Target.is_human_target T.target && not (Target.suppress_targets T.target !suppress_target_names) then
           targets_opt targets
         else
           emp) ^
        letbind false (Let_val (p, topt, sk, e), Ast.Unknown) ^
        break_hint_space 0 ^
        T.def_end
      else
        emp
  | Val_def(Fun_def(s1, rec_flag, targets, clauses)) ->
      if in_target targets then
        let (is_rec, is_real_rec, try_term) = Typed_ast_syntax.try_termination_proof T.target A.env.c_env d in
        let s2 = match rec_flag with FR_non_rec -> None | FR_rec sk -> sk in
        let rec clause_names ls =
          match ls with
            | [] -> []
            | (n,n_ref, _, _, _, _)::cs -> (Name.strip_lskip (B.const_ref_to_name n.term false n_ref)) :: clause_names cs
        in
        let ns = clause_names (Seplist.to_list clauses) in
          T.rec_def_header is_rec is_real_rec try_term s1 s2 ns ^
          (if Target.is_human_target T.target && not (Target.suppress_targets T.target !suppress_target_names) then
             targets_opt targets
           else
             emp) ^
          flat (Seplist.to_sep_list (funcl false) (sep T.def_sep) clauses) ^
          T.def_end ^
          T.rec_def_footer is_rec is_real_rec try_term ns
          else
        emp
  | Val_def(Let_inline(s1,s2,targets,n,c,args,s4,body)) ->
      if (is_human_target T.target) then
        ws s1 ^
        T.bkwd "let" ^
        ws s2 ^
        T.bkwd "inline" ^
        targets_opt targets ^
        Name.to_output Term_var n.term ^
        flat (List.map (fun n -> Name.to_output Term_var n.term) args) ^
        ws s4 ^
        kwd "=" ^
        core (exp false body)
      else
        emp
  | Lemma (sk0, lty, targets, (n, _), sk1, e) ->
      if (not (is_human_target T.target)) then emp else
      begin
      let lem_st = match lty with
                     | Ast.Lemma_theorem sk -> "theorem"
                     | Ast.Lemma_assert sk -> "assert"
                     | Ast.Lemma_lemma sk -> "lemma" in
      (ws sk0 ^ T.bkwd lem_st ^
       targets_opt targets ^
       Name.to_output Term_var n ^
       ws sk1 ^ kwd ":" ^
       core (exp false e))
    end
  | Module(s1,(n,l),mod_bind,s2,s3,ds,s4) ->
      ws s1 ^
      T.module_module ^
      Name.to_output Module_name n ^
      ws s2 ^
      kwd "=" ^
      ws s3 ^
      T.module_struct ^ (*meta "}" ^ *)
      flat (List.map (fun d -> def_internal callback true (match d with ((dreal,_),_,_) -> dreal) is_user_def) ds) ^
      (* THE ABOVE LINE WAS:  callback ds ^ *)
      ws s4 ^
      T.module_end
  | Rename(s1,(n,l),mod_bind,s2,m) ->
    	ws s1 ^
    	T.module_module ^
    	Name.to_output Module_name n ^
    	ws s2 ^
    	kwd "=" ^
    	Ident.to_output Module_name T.path_sep (B.module_id_to_ident m)
  | OpenImport (oi, ms) ->
  		let out =
  			let (ms', sk) = B.open_to_open_target ms in
      		open_import_def_to_output false oi Targets_opt_none ms' ^
      		ws sk
      in
  			if !suppress_libraries then
  				if Target.is_tex_target T.target then
  					emp
  				else
  					out
  			else
  				out
  | OpenImportTarget(oi, _, []) ->
  		let out = ws (oi_get_lskip oi) in
  			if !suppress_libraries then
  				if Target.is_tex_target T.target then
  					emp
  				else
  					out
  			else
  				out
  | OpenImportTarget(oi,targets, ms) ->
  		let out = open_import_def_to_output (is_human_target T.target) oi targets ms in
  			if !suppress_libraries then
  				if Target.is_tex_target T.target then
  					emp
  				else
  					out
  			else
  				out
  | Indreln(s,targets,names,clauses) ->
      if in_target targets then
        ws s ^
        T.reln_start ^
        (if Target.is_human_target T.target then
           targets_opt targets
         else
           emp) ^
        (if T.reln_show_types then
           flat (Seplist.to_sep_list indreln_name (sep T.reln_sep) names)
         else
           emp) ^
        flat (Seplist.to_sep_list indreln_clause (sep T.reln_sep) clauses) ^
        T.reln_end
      else
        emp
  | Val_spec(s1,(n,l),n_ref,ascii_opt,s2,(constraint_pre,t)) ->
      ws s1 ^
      T.val_start ^
      Name.to_output Term_var n ^
      val_ascii_opt ascii_opt ^
      ws s2 ^
      T.typ_sep ^
      begin
        match constraint_pre with
          | None -> emp
          | Some(cp) -> constraint_prefix cp
      end ^
      typ false t
  | Instance(inst_decl,i_ref,(cp,s2,id,class_path,t,s3),methods,s4) ->
      (match inst_decl with
        | Ast.Inst_decl s1 -> (ws s1 ^ T.bkwd "instance")
        | Ast.Inst_default s1 -> (ws s1 ^ T.bkwd "default_instance")
      ) ^
      begin
        match cp with
          | None -> emp
          | Some(cp) -> constraint_prefix cp
      end ^
      ws s2 ^
      kwd "(" ^
      Ident.to_output Class_name T.path_sep id ^
      typ false t ^
      ws s3 ^
      kwd ")" ^
      flat (List.map (fun d -> def_internal callback true (Val_def(d)) is_user_def) methods) ^
      ws s4 ^
      T.bkwd "end"
  | Class(cd,s2,(n,l), tv, class_path, s3, specs, s4) ->
      (match cd with
	| Ast.Class_decl s1 -> (ws s1 ^ T.bkwd "class")
	| Ast.Class_inline_decl (s1a, s1b)  -> (ws s1a ^ T.bkwd "class" ^ ws s1b ^ T.bkwd "inline")
      ) ^
      ws s2 ^
      kwd "(" ^
      Name.to_output Class_name n ^
      tyvar tv ^
      ws s3 ^
      kwd ")" ^
      flat (List.map
              (fun (s1,targets,(n,l),f_ref,ascii_rep_opt,s2,t) ->
                ws s1 ^
                T.val_start ^
                (if Target.is_human_target T.target then
                   targets_opt targets
                 else
                   emp) ^
                Name.to_output Term_method n ^
                val_ascii_opt ascii_rep_opt ^
                ws s2 ^
                kwd ":" ^
                typ false t)
              specs) ^
      ws s4 ^
      T.bkwd "end"
  | Declaration (Decl_target_rep_term (sk1, targ, sk2, comp, id, args, sk3, rhs)) ->
      if (not (Target.is_human_target T.target)) then emp else begin
        ws sk1 ^
        T.bkwd "declare" ^
        (Target.target_to_output targ) ^
        ws sk2 ^
        T.bkwd "target_rep" ^
        component_to_output comp ^
        (Ident.to_output (Term_const (false, false)) T.path_sep (B.const_id_to_ident id true)) ^
        (Output.concat emp (List.map (fun n -> Name.to_output Term_var n.term) args)) ^
        ws sk3 ^
        kwd "=" ^ core
        (match rhs with
          | Target_rep_rhs_term_replacement e -> exp true e
          | Target_rep_rhs_undefined -> emp
          | Target_rep_rhs_infix (sk1, decl, sk2, i) -> begin
               ws sk1 ^
               T.bkwd "infix" ^
               infix_decl decl ^
               backend true sk2 i
            end
          | Target_rep_rhs_special (sk1, sk2, st, eL) -> begin
               ws sk1 ^
               T.bkwd "special" ^
               ws sk2 ^
               str (Ulib.Text.of_string (T.string_escape st None)) ^
               Output.concat emp (List.map (exp false) eL)
            end
          | _ -> raise (Reporting_basic.err_todo true Ast.Unknown "declaration")
        )
      end
  | Declaration (Decl_target_rep_type (sk1, targ, sk2, sk3, id, args, sk4, rhs)) ->
      if (not (Target.is_human_target T.target)) then emp else begin
        ws sk1 ^
        T.bkwd "declare" ^
        (Target.target_to_output targ) ^
        ws sk2 ^
        T.bkwd "target_rep" ^
        ws sk3 ^
        T.bkwd "type" ^
        B.type_id_to_output id ^
        tdef_tvars true args ^
        ws sk4 ^
        kwd "=" ^
        core (typ true rhs)
      end
  | Declaration (Decl_target_sorts (sk1, targ, sk2, id, sk3, sorts)) ->
      if (not (Target.is_human_target T.target)) then emp else begin
        let sort = function
          | Sort (sk,None) -> ws sk ^ kwd "_"
          | Sort (sk,Some n) -> ws sk ^
             T.backend_quote (Name.to_output (Term_const (false, false))
                                (Name.add_lskip n))
        in
        ws sk1 ^
        T.bkwd "declare" ^
        (Target.target_to_output targ) ^
        ws sk2 ^
        T.bkwd "target_sorts" ^
        B.type_id_to_output id ^
        ws sk3 ^
        kwd "=" ^
        core (flat (List.map sort sorts))
      end
  | Declaration (Decl_ascii_rep (sk1, targets, sk2, comp, nk_id, sk3, sk4, n)) ->
      if (not (Target.is_human_target T.target)) then emp else begin
        ws sk1 ^
        T.bkwd "declare" ^
        targets_opt targets ^
        ws sk2 ^
        T.bkwd "ascii_rep" ^
        component_to_output comp ^
        nk_id_to_output nk_id ^
        ws sk3 ^
        kwd "=" ^
        ws sk4 ^
        core ((Name.to_output (Term_const (false, false)) (Name.add_pre_lskip sk4 (Name.add_lskip n))))
      end
  | Declaration (Decl_rename (sk1, targets, sk2, comp, nk_id, sk3, n)) ->
      if (not (Target.is_human_target T.target)) then emp else begin
        ws sk1 ^
        T.bkwd "declare" ^
        targets_opt targets ^
        ws sk2 ^
        T.bkwd "rename" ^
        component_to_output comp ^
        nk_id_to_output nk_id ^
        ws sk3 ^
        kwd "=" ^
        core (Name.to_output (Term_const (false, false)) n)
      end
  | Declaration (Decl_rename_current_module (sk1, targets, sk2, sk3, sk4, n)) ->
      if (not (Target.is_human_target T.target)) then emp else begin
        ws sk1 ^
        T.bkwd "declare" ^
        targets_opt targets ^
        ws sk2 ^
        T.bkwd "rename" ^
        ws sk3 ^
        T.bkwd "module" ^
        ws sk4 ^
        kwd "=" ^
        core (Name.to_output (Term_const (false, false)) n)
      end
  | Declaration (Decl_compile_message (sk1, targets, sk2, c_id, sk3, sk4, msg)) ->
      if (not (Target.is_human_target T.target)) then emp else begin
        ws sk1 ^
        T.bkwd "declare" ^
        targets_opt targets ^
        ws sk2 ^
        T.bkwd "compile_message" ^
        (Ident.to_output (Term_const (false, false)) T.path_sep (B.const_id_to_ident c_id true)) ^
        ws sk3 ^
        kwd "=" ^
        ws sk4 ^
        core (str (Ulib.Text.of_string (T.string_escape msg None)))
      end
  | Declaration (Decl_termination_argument (sk1, targets, sk2, c_id, sk3, term_arg)) ->
      if (not (Target.is_human_target T.target)) then emp else begin
        ws sk1 ^
        T.bkwd "declare" ^
        targets_opt targets ^
        ws sk2 ^
        T.bkwd "termination_argument" ^
        (Ident.to_output (Term_const (false, false)) T.path_sep (B.const_id_to_ident c_id true)) ^
        ws sk3 ^
        kwd "=" ^ core (
        match term_arg with
          | Ast.Termination_setting_automatic sk -> (ws sk ^ T.bkwd "automatic")
          | Ast.Termination_setting_manual sk -> (ws sk ^ T.bkwd "manual")
        )
      end
  | Declaration (Decl_pattern_match_decl (sk1, targs, sk2, ex_set, p_id, args, sk3, sk4, constr_ids, sk5, elim_id_opt)) ->
      if (not (Target.is_human_target T.target)) then emp else begin
        ws sk1 ^
        T.bkwd "declare" ^
        targets_opt targs ^
        ws sk2 ^
        T.bkwd "pattern_match" ^
        (match ex_set with
           | Ast.Exhaustivity_setting_exhaustive   sk -> ws sk ^ T.bkwd "exhaustive"
           | Ast.Exhaustivity_setting_inexhaustive sk -> ws sk ^ T.bkwd "inexhaustive"
        ) ^
        B.type_id_to_output p_id ^
        tdef_tvars true args ^
        ws sk3 ^
        kwd "=" ^
        ws sk4 ^
        kwd "[" ^
        flat
          (Seplist.to_sep_list_last Seplist.Optional (fun id ->
             (Ident.to_output (Term_const (false, false)) T.path_sep (B.const_id_to_ident id true))
           ) (sep (kwd ";")) constr_ids) ^
        ws sk5 ^
        kwd "]" ^
        Util.option_default_map elim_id_opt emp (fun id ->
          (Ident.to_output (Term_const (false, false)) T.path_sep (B.const_id_to_ident id true)))
      end
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
{\lemfoo{set\_option\_map} \;\tsunknown{f} \;\tsunknown{xs} = {}\\{}}    #5 full def
{\{ (\Mcase  \;\tsunknown{f} \;\tsunknown{x} \;\Mof ...  }               #6 core
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

and make_lemdefn latex_name latex_label typeset_name pre_comment full core post_comment =
  (r"\\newcommand{" ^^^^ latex_name ^^^^ r"}[1][default]{%\n" ^^^^
  r"\\lemdefn\n" ^^^^
  r"{#1}\n" ^^^^
  r"{" ^^^^ latex_label ^^^^ r"}\n" ^^^^
  r"{" ^^^^ typeset_name ^^^^ r"}\n" ^^^^
  r"{" ^^^^ pre_comment ^^^^ r"}\n" ^^^^
  r"{" ^^^^ full ^^^^ r"}\n" ^^^^
  r"{" ^^^^ core ^^^^ r"}\n" ^^^^
  r"{" ^^^^ post_comment ^^^^ r"}%\n" ^^^^
  r"}\n",
  latex_name ^^^^ r"\n")

and def_tex_inc callback (((d,ws_after),_, _):def) : (Ulib.Text.t*Ulib.Text.t) list =
begin
  let extract_comments ws = begin
    let rec aux rws ws  = begin
      match ws with
        | None -> (None, rws)
        | Some [] -> (None, rws)
        | Some (Ast.Com _ :: _) -> (ws, rws)
        | Some (x :: l) -> aux (Ast.combine_lex_skips rws (Some [x])) (Some l)
    end in
    let rev_ws ws = Util.option_map List.rev ws in

    let (ws', _) = aux None ws in
    match ws' with
      | None -> (* No comment comment found, so keep original stuff *) (ws, None)
      | _ -> begin
               let (ws'', end_ws) = aux None (rev_ws ws') in
               (rev_ws end_ws, rev_ws ws'')
             end
  end in
  match d with
  	| OpenImport _ when !suppress_libraries -> []
  	| OpenImportTarget _ when !suppress_libraries -> []
  	| _ ->
  let (d', comment_ws_pre) = def_aux_alter_init_lskips extract_comments d in
  let (_, comment_ws_post) = Util.option_default_map ws_after (None, None) extract_comments in

  let output_org = def_internal callback false d' false in
  let full_output = remove_core output_org in
  let core_output = concat space (extract_core output_org) in

  let (_, label_s, name_out) = def_to_label_formated_name d' in
  let label = r (latex_fresh_labels label_s) in
  let typeset_name = to_rope_tex name_out in

  let pre_comment = to_rope_tex (ws comment_ws_pre) in
  let post_comment = to_rope_tex (ws comment_ws_post) in
  let latex_name = Output.tex_command_name label in
  let latex_label = Output.tex_command_label label in
  let full = to_rope_tex full_output in
  let core = to_rope_tex core_output in
  [make_lemdefn latex_name latex_label typeset_name pre_comment full core post_comment]
end

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
              let has_sort = Seplist.exists (fun (_,_,_,t) -> is_type_with_sort t) fields in
              ws s1 ^
              T.typedefrec_start has_sort ^
              tdef_tctor false tvs (B.type_path_to_name n t_path) regex ^
              tyexp_rec s4 s5 fields s6 ^
              T.typedefrec_end has_sort
          | _ -> assert false
      end

  | Val_def ((Let_def(s1, targets,(p, name_map, topt,sk, e)) as def)) ->
      if in_target targets then
        ws s1 ^ kwd "definition" ^
        (if Target.is_human_target T.target then
           targets_opt targets
         else
           emp) ^
        isa_mk_typed_def_header (pat false p, [], sk, exp_to_typ e) ^
        kwd "where \n\\<open>" ^ pat false p ^ ws sk ^ kwd "= (" ^ exp false e ^ kwd ")\\<close>" ^ T.def_end
      else emp

  | Val_def ((Fun_def (s1, rec_flag, targets, clauses) as def)) ->
      let (is_rec, is_real_rec, try_term) = Typed_ast_syntax.try_termination_proof T.target A.env.c_env d in
      if in_target targets then
        let is_simple = not is_rec && (match Seplist.to_list clauses with
          | [(_, _, ps, _, _, _)] -> List.for_all (fun p -> (Pattern_syntax.is_var_wild_pat p)) ps
          | _ -> false)
        in
        let s2 = match rec_flag with FR_non_rec -> None | FR_rec sk -> sk in
        ws s1 ^ kwd (if (is_rec && not try_term) then "function (sequential,domintros)" else (if is_simple then "definition" else "fun")) ^ ws s2 ^
        (isa_funcl_header_seplist clauses) ^
        flat (Seplist.to_sep_list (isa_funcl_default (kwd "= ")) (sep T.def_sep) clauses) ^
        (if (is_rec && not try_term) then (kwd "\nby pat_completeness auto") else emp) ^
              new_line
      else emp

  | Val_spec(s1,(n,l),n_ref,_,s2,t) ->
      raise (Reporting_basic.err_todo false l "Isabelle: Top-level type constraints omited; should not occur at the moment")

  (* TODO INDRELN THe names should be output *)
  | Indreln(s,targets,names,clauses) ->
      if in_target targets then
        ws s ^
        T.reln_start ^
        isa_funcl_header_indrel_seplist clauses ^
        flat (Seplist.to_sep_list indreln_clause (sep T.reln_sep) clauses) ^
        T.reln_end
      else
        emp

  | _ -> remove_core (def_internal callback inside_module d is_user_def)

and def callback (inside_module : bool) d is_user_def =
  match T.target with
   | Target_no_ident Target_isa  -> remove_core (isa_def callback inside_module d is_user_def)
   | Target_no_ident Target_tex  ->
        if inside_module then
           remove_core (def_internal callback inside_module d is_user_def)
        else begin
          meta "\\lemdef{" ^  remove_core (def_internal callback inside_module d is_user_def) ^ meta "}\n"
        end
   | Target_no_ident Target_html -> html_link_def d ^ remove_core (def_internal callback inside_module d is_user_def)
   | _ -> remove_core (def_internal callback inside_module d is_user_def)
end


module F(T : Target)(A : sig val avoid : var_avoid_f option;; val env : env;; val dir : string end)(X : sig val comment_def : def -> Ulib.Text.t end) = struct

let (^^^^) = Ulib.Text.(^^^)

let output_to_rope out = to_rope T.string_quote T.lex_skip T.need_space out

module F' = F_Aux(T)(struct let avoid = A.avoid;; let env = A.env;; let ascii_rep_set = Types.Cdset.empty;; let dir = A.dir end)(X)

module C = Exps_in_context (struct
  let env_opt = Some A.env
  let avoid = A.avoid
end);;

module CdsetE = Util.ExtraSet(Types.Cdset)

let exp_to_rope e = output_to_rope (F'.exp false e)
let pat_to_rope p = output_to_rope (F'.pat false p)
let src_t_to_rope t = output_to_rope (F'.typ false t)
let typ_to_rope t = src_t_to_rope (C.t_to_src_t t)

let rec defs (ds:def list) =
  List.fold_right
    (fun ((d,s),l,lenv) y ->
       begin
        let ue = add_def_entities T.target true empty_used_entities ((d,s),l,lenv) in
        let module F' = F_Aux(T)(struct let avoid = A.avoid;; let env = { A.env with local_env = lenv };; let dir = A.dir;;
					let ascii_rep_set = CdsetE.from_list ue.used_consts end)(X) in
        let (before_out, d') = Backend_common.def_add_location_comment ((d,s),l,lenv) in
        before_out ^ F'.def defs false d' (is_pp_loc l)
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

let defs_to_rope ((ds:def list),end_lex_skips) =
  match T.target with
  | Target_no_ident Target_tex ->
      (to_rope_tex (defs ds) ^^^^
      (match to_rope_option_tex ((* add empty stuff before last comment to prevent stripping of empty lines *) kwd "" ^ ws end_lex_skips) with None -> r"" | Some rr ->
        r"\\lemdef{%\n" ^^^^
        rr  ^^^^
        r"%\n}\n"
      ))
  | _ -> output_to_rope (defs ds ^ ws end_lex_skips)

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
   				        let dir = A.dir;;
					let ascii_rep_set = CdsetE.from_list ue.used_consts end)(X) in
        batrope_pair_concat (F'.def_tex_inc defs ((d,s), l, lenv))) ds)
  | _ ->
      raise (Failure "defs_inc called on non-tex target")

let defs_to_extra_aux gf (ds:def list) =
    List.fold_right
      (fun ((d,s),l,lenv) y ->
         begin
           let ue = add_def_entities T.target true empty_used_entities ((d,s),l,lenv) in
           let module F' = F_Aux(T)(struct let avoid = A.avoid;; let env = { A.env with local_env = lenv };; let dir = A.dir;;
                                           let ascii_rep_set = CdsetE.from_list ue.used_consts end)(X) in
           remove_core (match T.target with
           | Target_no_ident Target_isa   -> F'.isa_def_extra gf d l
           | Target_no_ident Target_hol   -> F'.hol_def_extra gf d l
           | Target_no_ident Target_ocaml -> F'.ocaml_def_extra gf d l
           | _ -> emp)
         end ^ y
      )
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
            let dir = A.dir
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

module Make(A : sig val avoid : var_avoid_f;; val env : env;; val dir : string end) = struct
  module Dummy = struct let comment_def d = assert false end

  module C = struct let env = A.env;; let avoid = Some(A.avoid)
            let dir = A.dir end

  let ident_defs defs =
    let module B = F(Identity)(C)(Dummy) in
      B.defs_to_rope defs

  let lem_defs defs =
    let module B = F(Lem)(C)(Dummy) in
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
    let module B = F(Isa())(C)(Comment_def) in
      (B.defs_to_rope defs, B.defs_to_extra defs)

  let isa_header_defs defs =
    let module B = F(Isa())(C)(Comment_def) in
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
