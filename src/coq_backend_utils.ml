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

open Output
open Typed_ast

let r = Ulib.Text.of_latin1
;;

let ($) f x = f x
;;

let (|>) f g = fun x -> g (f x)
;;

let rec nub =
  function
    | []    -> []
    | x::xs ->
        if List.mem x xs then
          nub xs
        else
          x::nub xs
;;

let rec take_while p l =
  match l with
    | []    -> []
    | x::xs ->
        if p x then
          x::take_while p xs
        else
          take_while p xs
;;

let rec drop_while p l =
  match l with
    | []    -> []
    | x::xs ->
        if p x then
          drop_while p xs
        else
          x::drop_while p xs
;;

let rec iterate i n =
  match n with
    | 0 -> []
    | n -> i :: iterate i (n - 1)
;;

let span p l = (take_while p l, drop_while p l)
;;

let rec group_with p l =
  match l with
    | []    -> []
    | x::xs ->
        let (ys, zs) = span (p x) xs in
          (x::ys)::group_with p zs
;;

let rec intercalate sep =
  function
    | [] -> []
    | [x] -> [x]
    | x::xs -> x::sep::intercalate sep xs
;;

let mapi f xs =
	let rec go counter f =
		function
			| []    -> []
			| x::xs -> f counter x :: go (counter + 1) f xs
	in
		go 0 f xs
;;

let from_string x = meta x
;;

let sep x s = ws s ^ x
;;

let tyvar (_, tv, _) = id Type_var (Ulib.Text.(^^^) (r"") tv)
;;

let path_sep = from_string "."
;;

let all p l =
  List.fold_right (&&) (List.map p l) true
;;

let any p l =
  List.fold_right (||) (List.map p l) false
;;

let separate sep l =
  List.fold_right (^) (intercalate (from_string sep) l) emp
;;

let combine l =
    List.fold_right (^) l emp
;;

let lskips_t_to_output name =
  let stripped = Name.strip_lskip name in
  let rope = Name.to_rope stripped in
    Output.id Term_var rope
;;