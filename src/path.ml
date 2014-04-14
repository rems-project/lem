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

type t = 
  | Path_def of Name.t list * Name.t
  | Path_list
  | Path_bool
  | Path_nat 
  | Path_numeral
  | Path_bit
  | Path_set
  | Path_vector
  | Path_char
  | Path_string
  | Path_unit

let mk_path ns n = Path_def(ns,n)

let mk_path_list names =
  let (ns, n) = Util.list_dest_snoc names in
  mk_path ns n


let r = Ulib.Text.of_latin1

let to_name_list =
    let build s = ([], Name.from_rope (r s)) in
    let lst = build "list" in
    let bln = build "bool" in
    let bit = build "bit" in
    let nat = build "nat" in
    let set = build "set" in
    let vec = build "vector" in
    let str = build "string" in
    let unt = build "unit" in
    let chr = build "char" in
    let num = build "numeral" in
    function
    | Path_def (vs,v) -> (vs,v)
    | Path_list    -> lst
    | Path_bool    -> bln
    | Path_bit     -> bit
    | Path_nat     -> nat
    | Path_set     -> set
    | Path_vector  -> vec
    | Path_string  -> str
    | Path_unit    -> unt
    | Path_char    -> chr
    | Path_numeral -> num

let from_id id = 
  let (x,y) = Ident.to_name_list id in 
    Path_def(x,y)

let compare p1 p2 = 
  match (to_name_list p1,to_name_list p2) with
      ((ns1,n1), (ns2,n2)) -> Util.compare_list Name.compare (ns1@[n1]) (ns2@[n2])

let pp ppf p =
  match (to_name_list p) with
    | ([],v) ->
        Name.pp ppf v
    | (vs,v) ->
        fprintf ppf "%a.%a" 
          (lst "." Name.pp) vs
          Name.pp v

let to_string p =
  pp_to_string (fun ppf -> pp ppf p)

let flat = function
  | [] -> r""
  | r2 -> Ulib.Text.concat (r"") r2

let (^) = Ulib.Text.(^^^)

let to_ident sk p =  match to_name_list p with 
     (vs,v) -> Ident.mk_ident sk vs v

let natpath = Path_nat
let boolpath = Path_bool
let bitpath = Path_bit
let listpath = Path_list
let setpath = Path_set
let vectorpath = Path_vector
let stringpath = Path_string
let unitpath = Path_unit
let charpath = Path_char
let numeralpath = Path_numeral

let check_prefix n p = match p with
  | Path_def(n2::_,_) ->
      Name.compare n n2 = 0
  | _ -> false

let get_toplevel_name p = match (to_name_list p) with
  | ([]  ,n) -> n
  | (n::_,_) -> n
           
let to_name p = match to_name_list p with
  | ([],n) -> n
  | (ns,n) ->
      Name.from_rope 
        (Ulib.Text.concat (r"_") (List.map Name.to_rope ns @ [Name.to_rope n]))

let get_name p = match to_name_list p with (_,x) -> x

let get_module_path p =
  let (ms, _) = to_name_list p in
  if (Util.list_null ms) then None else
  Some (mk_path_list ms)

