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

open Format
open Pp

(* These compare faster than Ulib.Text.t *)
(*
type t = Ulib.UTF8.t
let compare r1 r2 = 
  Ulib.UTF8.compare r1 r2

let from_rope r = Ulib.Text.to_string r

let to_rope n = Ulib.Text.of_string n
let to_string = Ulib.UTF8.to_string
*)

type t = string
let compare r1 r2 = 
  Pervasives.compare r1 r2

let from_rope r = Ulib.Text.to_string r

let to_rope n = Ulib.Text.of_string n
let to_string n = n
let from_string n = n

  (*
type t = Ulib.Text.t
let compare r1 r2 = 
  if r1 == r2 then 
    0 
  else 
    Ulib.Text.compare r1 r2

let from_rope r = r

let to_rope n = n
let to_string n = Ulib.Text.to_string n
   *)

let (^) = Ulib.Text.(^^^)

let fresh_start start s ok =
  let rec f (n:int) =
    let name = s ^ Ulib.Text.of_latin1 (string_of_int n) in
      if ok (from_rope name) then 
        name
      else
        f (n + 1)
  in
  let x = s in
    match start with
      | None ->
          if ok (from_rope x) then
            x 
          else
            f 0
      | Some(i) ->
          f i

let fresh s ok = from_rope (fresh_start None s ok)

let rec fresh_list i s ok =
  if i = 0 then
    []
  else begin
    let new_name = from_rope (fresh_start (Some(i)) s ok) in
    let new_ok n = ok n && (n <> new_name) in
    new_name :: fresh_list (i - 1) s new_ok
  end




let rename f r = from_rope (f (to_rope r))

let pp ppf n = pp_str ppf (to_string n)

let starts_with_upper_letter x = 
  try 
    let c = Ulib.UChar.char_of (Ulib.UTF8.get x 0) in
      Str.string_match (Str.regexp "[A-Z]") (String.make 1 c) 0
  with 
    | Ulib.UChar.Out_of_range -> false

let starts_with_underscore x = 
  try 
    (String.length x > 1) && (Ulib.UChar.char_of (Ulib.UTF8.get x 0) = '_')
  with 
    | Ulib.UChar.Out_of_range -> false

let remove_underscore x = 
  if (starts_with_underscore x) then
     Some (from_rope (let r = (to_rope x) in Ulib.Text.sub r 1 (Ulib.Text.length r -1)))
  else None

let starts_with_lower_letter x = 
  try 
    let c = Ulib.UChar.char_of (Ulib.UTF8.get x 0) in
      Str.string_match (Str.regexp "[a-z]") (String.make 1 c) 0
  with 
    | Ulib.UChar.Out_of_range -> false

let uncapitalize x = 
  if (starts_with_upper_letter x) then
    let c = Ulib.UChar.of_char (Char.lowercase (Ulib.UChar.char_of (Ulib.UTF8.get x 0))) in
    Some (from_rope (Ulib.Text.set (to_rope x) 0 c))
  else None

let capitalize x =
  if (starts_with_lower_letter x) then
    let c = Ulib.UChar.of_char (Char.uppercase (Ulib.UChar.char_of (Ulib.UTF8.get x 0))) in
    Some (from_rope (Ulib.Text.set (to_rope x) 0 c))
  else None

type lskips_t = Ast.lex_skips * Ulib.Text.t 

let r = Ulib.Text.of_latin1

let from_ix = function 
  | Ast.SymX_l((s,x),l) -> (s,x)

let from_x = function 
  | Ast.X_l((s,x),l) -> (s,x)
  | Ast.PreX_l(s,(_,x),_,_) ->  (s, x) (* TODO: check the missing parenthesis information is not important *)


let strip_lskip (_,x) = from_rope x
let add_lskip n = (None,to_rope n)

let star = Ulib.Text.of_latin1 "*"
let space = Output.ws (Some [Ast.Ws (Ulib.Text.of_latin1 " ")])

let to_output a (s,x) = Output.(^) (Output.ws s) (Output.id a x)

let to_output_infix infix_f a (s,x) = Output.(^) (Output.ws s) (infix_f a x)

let to_output_quoted a (s,x)= 
  let open Output in
  let (^^) = Ulib.Text.(^^^) in
  to_output a (s, (r"\"" ^^ x ^^ r"\""))

let to_rope_tex a n = 
  Output.to_rope_ident a (to_rope n)

let add_pre_lskip lskip (s,x) = 
  (Ast.combine_lex_skips lskip s,x)

let get_lskip (s,x) = s

let lskip_pp ppf (s,x) = 
        Format.fprintf ppf "%a%a" 
          Ast.pp_lex_skips s
          pp (from_rope x)

let lskip_rename f (s,x) =
  (s,f x)

let replace_lskip (s,x) s_new = 
  (s_new,x)

