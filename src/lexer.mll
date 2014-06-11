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

{
open Parser
module M = Map.Make(String)
exception LexError of char * Lexing.position

let (^^^) = Ulib.Text.(^^^)
let r = Ulib.Text.of_latin1

let parse_int lexbuf i =
  try (int_of_string i, i)
  with Failure "int_of_string" ->
    raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax (
           Lexing.lexeme_start_p lexbuf,
           "couldn't parse integer "^i)))

(* Update the current location with file name and line number. *)
let update_loc lexbuf file line =
  let pos = lexbuf.Lexing.lex_curr_p in
  let new_file = match file with
    | None -> pos.Lexing.pos_fname
    | Some s -> s
  in
  lexbuf.Lexing.lex_curr_p <- { pos with
    Lexing.pos_fname = new_file;
    Lexing.pos_lnum = line;
    Lexing.pos_bol = pos.Lexing.pos_cnum;
  };;


let kw_table = 
  List.fold_left
    (fun r (x,y) -> M.add x y r)
    M.empty
    [("as",                      (fun x -> As(x)));
     ("fun",                     (fun x -> Fun_(x)));
     ("function",                (fun x -> Function_(x)));
     ("with",                    (fun x -> With(x)));
     ("match",                   (fun x -> Match(x)));
     ("let",                     (fun x -> Let_(x)));
     ("and",                     (fun x -> And(x)));
     ("in",                      (fun x -> In(x)));
     ("of",                      (fun x -> Of(x)));
     ("rec",                     (fun x -> Rec(x)));
     ("type",                    (fun x -> Type(x)));
     ("module",                  (fun x -> Module_(x)));
     ("rename",                  (fun x -> Rename(x)));
     ("struct",                  (fun x -> Struct(x)));
     ("end",                     (fun x -> End(x)));
     ("open",                    (fun x -> Open_(x)));
     ("import",                  (fun x -> Import_(x)));
     ("include",                 (fun x -> Include_(x)));
     ("true",                    (fun x -> True(x)));
     ("false",                   (fun x -> False(x)));
     ("begin",                   (fun x -> Begin_(x)));
     ("if",                      (fun x -> If_(x)));
     ("then",                    (fun x -> Then(x)));
     ("else",                    (fun x -> Else(x)));
     ("val",                     (fun x -> Val(x)));
     ("class",                   (fun x -> Class_(x)));
     ("instance",                (fun x -> Inst(x)));
     ("default_instance",        (fun x -> Inst_default(x)));
     ("indreln",                 (fun x -> Indreln(x)));
     ("forall",                  (fun x -> Forall(x)));
     ("exists",                  (fun x -> Exists(x)));
     ("inline",                  (fun x -> Inline(x)));
     ("lem_transform",           (fun x -> Lem_transform(x)));
     ("IN",                      (fun x -> IN(x,r"IN")));
     ("MEM",                     (fun x -> MEM(x,r"MEM")));
     ("declare",                 (fun x -> Declare(x)));
     ("infix",                   (fun x -> Infix(x)));
     ("field"),                  (fun x -> Field(x));
     ("automatic"),              (fun x -> Automatic(x));
     ("manual"),                 (fun x -> Manual(x));
     ("exhaustive"),             (fun x -> Exhaustive(x));
     ("inexhaustive"),           (fun x -> Inexhaustive(x));
     ("ascii_rep"),              (fun x -> AsciiRep(x));
     ("compile_message"),        (fun x -> CompileMessage(x));
     ("set_flag"),               (fun x -> SetFlag(x));
     ("termination_argument"),   (fun x -> TerminationArgument(x));
     ("pattern_match"),          (fun x -> PatternMatch(x));
     ("right_assoc"),            (fun x -> RightAssoc(x));
     ("left_assoc"),             (fun x -> LeftAssoc(x));
     ("non_assoc"),              (fun x -> NonAssoc(x));
     ("non_exec"),               (fun x -> NonExec(x));
     ("special"),                (fun x -> Special(x));
     ("target_rep"),             (fun x -> TargetRep(x));
     ("target_type",             (fun x -> TargetType(x)));
     ("target_const",            (fun x -> TargetConst(x)));
     ("lemma",                   (fun x -> Lemma(x)));
     ("assert",                  (fun x -> Assert(x)));
     ("theorem",                 (fun x -> Theorem(x)));
     ("do",                      (fun x -> Do(x)));
     ("witness",		 (fun x -> Witness(x)));
     ("check",			 (fun x -> Check(x)));
]

}

let ws = [' ''\t']+
let letter = ['a'-'z''A'-'Z']
let digit = ['0'-'9']
let binarydigit = ['0'-'1']
let octdigit = ['0'-'7']
let hexdigit = ['0'-'9''A'-'F''a'-'f']
let alphanum = letter|digit
let startident = letter|'_'
let ident = alphanum|['_''\'']
let quote = [^' ''\t''\n''`''"']
let oper_char = ['!''$''%''&''*''+''-''.''/'':''<''=''>''?''@''^''|''~']
let safe_com1 = [^'*''('')''\n']
let safe_com2 = [^'*''(''\n']
let com_help = "("*safe_com2 | "*"*"("+safe_com2 | "*"*safe_com1
let com_body = com_help*"*"*
let escape_sequence = ('\\' ['\\''\"''\'''n''t''b''r']) | ('\\' digit digit digit) | ('\\' 'x' hexdigit hexdigit)
let char = letter|digit|[' ''!''#''$''%''&''('')''*''+'',''-''.''/'':'';''<''=''>''?''@''['']''^''_''{''}''|''~']|escape_sequence


rule token skips = parse
  | ws as i
    { token (Ast.Ws(Ulib.Text.of_latin1 i)::skips) lexbuf }
  | "\n"
    { Lexing.new_line lexbuf;
      token (Ast.Nl::skips) lexbuf } 
  | "#" [' ' '\t']* (['0'-'9']+ as num) [' ' '\t']* ("\"" ([^ '\010' '\013' '"' ]* as name) "\"")? [^ '\010' '\013']* "\n"
                                        { update_loc lexbuf name (int_of_string num);
                                          token [] lexbuf }  
  | "."                                 { (Dot(Some(skips))) }

  | "("                                 { (Lparen(Some(skips))) }
  | ")"                                 { (Rparen(Some(skips))) }
  | ","                                 { (Comma(Some(skips))) }
  | "@"					{ (At(Some(skips),r"@")) }
  | "_"                                 { (Under(Some(skips))) }
  | "*"                                 { (Star(Some(skips),r"*")) }
  | "+"					{ (Plus(Some(skips),r"+")) }
  | ">="				{ (GtEq(Some(skips),r">=")) }
  | ":"                                 { (Colon(Some(skips))) }
  | "~{"                                { (NegLcurly(Some(skips))) }
  | "{"                                 { (Lcurly(Some(skips))) }
  | "}"                                 { (Rcurly(Some(skips))) }
  | ";"                                 { (Semi(Some(skips))) }
  | "["                                 { (Lsquare(Some(skips))) }
  | "]"                                 { (Rsquare(Some(skips))) }
  | "="                                 { (Eq(Some(skips),r"=")) }
  | "|"                                 { (Bar(Some(skips))) }
  | "->"                                { (Arrow(Some(skips))) }
  | ";;"                                { (SemiSemi(Some(skips))) }
  | "::" as i                           { (ColonColon(Some(skips),Ulib.Text.of_latin1 i)) }
  | "&&" as i                           { (AmpAmp(Some(skips),Ulib.Text.of_latin1 i)) }
  | "||" as i                           { (BarBar(Some(skips),Ulib.Text.of_latin1 i)) }
  | "=>"                                { (EqGt(Some(skips))) }

  | "==>"                               { (EqEqGt(Some(skips))) }
  | "-->" as i                          { (MinusMinusGt(Some(skips),Ulib.Text.of_latin1 i)) }
  | "<|"                                { (LtBar(Some(skips))) }
  | "|>"                                { (BarGt(Some(skips))) }

  | "[|"				{ (BraceBar(Some(skips))) }
  | "|]"				{ (BarBrace(Some(skips))) }
  | ".["				{ (DotBrace(Some(skips))) }

  | "#0"				{ (HashZero(Some(skips))) }
  | "#1"				{ (HashOne(Some(skips))) }
  | "<-"                                { (LeftArrow(Some(skips))) }
  | "union" as i                        { (PlusX(Some(skips),Ulib.Text.of_latin1 i)) }
  | "inter" as i                        { (StarX(Some(skips),Ulib.Text.of_latin1 i)) }
  | "subset" | "\\" | "NIN" as i        { (EqualX(Some(skips),Ulib.Text.of_latin1 i)) }
  | "lsl" | "lsr" | "asr" as i          { (StarstarX(Some(skips), Ulib.Text.of_latin1 i)) }
  | "mod" | "div" | "land" | "lor" | "lxor" as i  { (StarX(Some(skips), Ulib.Text.of_latin1 i)) }


  | "(*"                           
    { token (Ast.Com(Ast.Comment(comment (Lexing.lexeme_start_p lexbuf) lexbuf))::skips) lexbuf }

  | startident ident* as i              { if M.mem i kw_table then
                                            (M.find i kw_table) (Some(skips))
                                          else
                                            X(Some(skips), Ulib.Text.of_latin1 i) }

  | "\\\\" ([^' ' '\t' '\n']+ as i)     { (X(Some(skips), Ulib.Text.of_latin1 i)) } 

  | "`" (quote* as i) "`"              { BacktickString(Some skips, i) }

  | "'" (startident ident* as i)        { (Tyvar(Some(skips), Ulib.Text.of_latin1 i)) }
  | "''" (startident ident* as i)	{ (Nvar(Some(skips), Ulib.Text.of_latin1 i)) }
  | ['!''?''~'] oper_char* as i         { (X(Some(skips), Ulib.Text.of_latin1 i)) }

  | "**" oper_char* as i                { (StarstarX(Some(skips), Ulib.Text.of_latin1 i)) }
  | ['/''%'] oper_char* as i         { (StarX(Some(skips), Ulib.Text.of_latin1 i)) }
  | "*" oper_char+ as i         { (StarX(Some(skips), Ulib.Text.of_latin1 i)) }
  | ['+''-'] oper_char* as i            { (PlusX(Some(skips), Ulib.Text.of_latin1 i)) }
  | ">=" oper_char+ as i   		{ (GtEqX(Some(skips), Ulib.Text.of_latin1 i)) }
  | ['@''^'] oper_char* as i            { (AtX(Some(skips), Ulib.Text.of_latin1 i)) }
  | ['=''<''>''|''&''$'] oper_char* as i { (EqualX(Some(skips), Ulib.Text.of_latin1 i)) }
  | digit+ as i                         { Num(Some(skips),parse_int lexbuf i) }
  | "0B" binarydigit+ as i		{ BinNum(Some(skips), parse_int lexbuf i) }
  | "0O" octdigit+ as i 		{ OctNum(Some(skips), parse_int lexbuf i) }
  | "0X" hexdigit+ as i 		{ HexNum(Some(skips), parse_int lexbuf i) }

  | "0b" (binarydigit+ as i)		{ (Bin(Some(skips), i)) }
  | "0x" (hexdigit+ as i) 		{ (Hex(Some(skips), i)) }
  | '"'                                 { (String(Some(skips),
                                           string (Lexing.lexeme_start_p lexbuf) (Buffer.create 10) lexbuf)) }
  | "#\'" (char as i) '\''               { (Char(Some(skips), i)) }
  | eof                                 { (Eof(Some(skips))) }
  | _  as c                             { raise (LexError(c, Lexing.lexeme_start_p lexbuf)) }


and comment pos = parse
  | (com_body "("* as i) "(*"           { let c1 = comment pos lexbuf in
                                          let c2 = comment pos lexbuf in
                                            Ast.Chars(Ulib.Text.of_latin1 i) :: Ast.Comment(c1) :: c2}
  | (com_body as i) "*)"                { [Ast.Chars(Ulib.Text.of_latin1 i)] }
  | com_body "("* "\n" as i             { Lexing.new_line lexbuf; 
                                          (Ast.Chars(Ulib.Text.of_latin1 i) :: comment pos lexbuf) }
  | _  as c                             { raise (LexError(c, Lexing.lexeme_start_p lexbuf)) }
  | eof                                 { raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax (pos,
                                            "Comment not terminated"))) }

and string pos b = parse
  | ([^'"''\n''\\']*'\n' as i)          { Lexing.new_line lexbuf;
                                          Buffer.add_string b i;
                                          string pos b lexbuf }
  | ([^'"''\n''\\']* as i)              { Buffer.add_string b i; string pos b lexbuf }
  | escape_sequence as i                { Buffer.add_string b i; string pos b lexbuf }
  | '\\' '\n' ws                        { Lexing.new_line lexbuf; string pos b lexbuf }
  | '\\'                                { raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax (pos,
                                            "illegal backslash escape in string"))) }
  | '"'                                 { let s = Buffer.contents b in
                                          try Ulib.UTF8.validate (Util.unescaped s); s
                                          with Ulib.UTF8.Malformed_code ->
                                            raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax (pos,
                                              "String literal is not valid utf8"))) }
  | eof                                 { raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax (pos,
                                            "String literal not terminated"))) }
