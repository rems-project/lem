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

exception No_type of Ast.l * string

let raise_error l msg pp n =
  let pp ppf = Format.fprintf ppf "%s: %a" msg pp n in
    raise (No_type(l, Pp.pp_to_string pp))

let raise_error_string l msg =
    raise (No_type(l, msg))

(* None of the Name.lskips_t can actually have any lskips, but the last one
 * might have parentheses, so Name.t isn't suitable *)
type t = Ast.lex_skips * Name.lskips_t list * Name.lskips_t

let pp ppf (sk,ns,n) =
  fprintf ppf "%a" 
    (Pp.lst "." Name.lskip_pp) (ns @ [n])


let error_pp_help ppf (n,sk) =
  fprintf ppf "%a%a" 
    Name.lskip_pp n
    Ast.pp_lex_skips sk

let error_pp ppf (sk,ns,n) =
  fprintf ppf "%a" 
    (Pp.lst "." error_pp_help) (ns @ [n])


let mk_ident m n l : t = 
  let ms = List.map (fun (n,sk) -> n) m in
  let prelim_id = (None, m, (n,None)) in
    List.iter (fun (_, sk) ->
                 if sk <> None && sk <> Some([]) then
                   raise_error l "illegal whitespace in identifier"
                     error_pp prelim_id)
      m;
    match ms with
      | [] ->
          (Name.get_lskip n, [], Name.replace_lskip n None)
      | m'::ms' ->
          List.iter 
            (fun n ->
               if Name.get_lskip n <> None && Name.get_lskip n <> Some([]) then
                 raise_error l "illegal whitespace in identifier"
                   error_pp prelim_id 
               else
                 ())
            (ms' @ [n]);
          (Name.get_lskip m', Name.replace_lskip m' None::ms', n)

let from_id (Ast.Id(m,xl,l)) : t =
  mk_ident 
    (List.map (fun (xl,l) -> (Name.from_x xl, l)) m)
    (Name.from_x xl)
    l

let get_name (_,_,x) = x

let (^) = Output.(^)

let to_output ident_f a sep ((sk,ns,n):t) = 
  Output.ws sk ^ Output.concat sep (List.map (Name.to_output ident_f a) (ns@[n]))

let drop_parens gp ((sk,ns,n):t) =
  if ns = [] then
    (sk, [], Name.drop_parens n)
  else if Precedence.is_infix (Name.get_prec gp n) then
    (sk,ns,Name.add_parens n)
  else
    (sk,ns,Name.drop_parens n)

let add_parens gp ((sk,ns,n):t) =
  if ns = [] then
    (sk, [], Name.add_parens n)
  else if Precedence.is_infix (Name.get_prec gp n) then
    (sk,ns,Name.add_parens n)
  else
    (sk,ns,Name.drop_parens n)

      (*
let capitalize (ns,n) = (ns,Name.capitalize n)

let uncapitalize (ns,n) = (ns,Name.uncapitalize n)

let starts_with_lower_letter (ns,n) = Name.starts_with_lower_letter n

let starts_with_upper_letter (ns,n) = Name.starts_with_upper_letter n

       *)

let replace_first_lskip ((sk,ns,n):t) s = 
  (s,ns,n)

let get_first_lskip ((sk,ns,n):t) =
  sk
                  
let get_prec gp (sk,l,i) =
  if l = [] then
    Name.get_prec gp i
  else
    Precedence.not_infix

let to_name_list ((sk,ns,n):t) =
  (List.map Name.strip_lskip ns, Name.strip_lskip n)

let strip_path name ((sk,ns,n) :t) : t =
  match ns with
    | [] -> 
        (sk,[],n)
    | (h::t) ->
        if Name.compare name (Name.strip_lskip h) = 0 then
          (sk,t, n)
        else
          (sk,ns,n)
