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

type t = Ast.lex_skips * Name.t list * Name.t

let pp ppf (sk,ns,n) =
  fprintf ppf "%a" 
    (Pp.lst "." Name.pp) (ns @ [n])

let to_string t =
  pp_to_string (fun ppf -> pp ppf t)

let error_pp_help ppf (n,sk) =
  fprintf ppf "%a%a" 
    Name.lskip_pp n
    Ast.pp_lex_skips sk

let error_pp ppf (sk,ns,n) =
  fprintf ppf "%a" 
    (Pp.lst "." error_pp_help) (ns @ [n])

let mk_ident_ast m n l : t = 
  let ms = List.map (fun (n,sk) -> n) m in
  let prelim_id = (None, m, (n,None)) in
    List.iter (fun (_, sk) ->
                 if sk <> None && sk <> Some([]) then
                   raise (Reporting_basic.err_type_pp l "illegal whitespace in identifier"
                     error_pp prelim_id))
      m;
    match ms with
      | [] ->
          (Name.get_lskip n, [], Name.strip_lskip n)
      | m'::ms' ->
          List.iter 
            (fun n ->
               if Name.get_lskip n <> None && Name.get_lskip n <> Some([]) then
                 raise (Reporting_basic.err_type_pp l "illegal whitespace in identifier"
                   error_pp prelim_id)
               else
                 ())
            (ms' @ [n]);
          (Name.get_lskip m', List.map Name.strip_lskip (m'::ms'), Name.strip_lskip n)

let mk_ident sk m n = ((sk, m, n) : t)

let from_name n = (Name.get_lskip n, [], Name.strip_lskip n)

let mk_ident_strings l i =
  mk_ident None (List.map (fun n -> Name.from_string n) l) (Name.from_string i) 

let from_id (Ast.Id(m,xl,l)) : t =
  mk_ident_ast
    (List.map (fun (xl,l) -> (Name.from_x xl, l)) m)
    (Name.from_x xl)
    l

let get_name (_,_,x) = Name.add_lskip x

let (^) = Output.(^)

let to_output_format ident_f a sep ((sk,ns,n):t) =
  let name_ropes = List.map Name.to_rope (ns @ [n]) in
  let o = ident_f a (Ulib.Text.concat sep name_ropes) in
  Output.ws sk ^ o

let to_output = to_output_format Output.id

let replace_lskip ((sk,ns,n):t) s = (s,ns,n)
let get_lskip ((sk,ns,n):t) = sk                
let to_name_list ((sk,ns,n):t) = (ns, n)

let has_empty_path_prefix ((sk,ns,n):t) = (List.length ns = 0)

let strip_path name ((sk,ns,n) :t) : t =
  match ns with
    | [] -> 
        (sk,[],n)
    | (h::t) ->
        if Name.compare name h = 0 then
          (sk,t, n)
        else
          (sk,ns,n)


let rename (sk,ns,n) n' = (sk,ns,n')

let drop_path (sk, _, n) = (sk, [], n)
