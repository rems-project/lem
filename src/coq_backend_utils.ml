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

(* Backward compatibility functions *)

(* Available in OCaml since 4.00.0 - copied from list.ml *)
let rec mapi i f = function
    [] -> []
  | a::l -> let r = f i a in r :: mapi (i + 1) f l
;;
let mapi f l = mapi 0 f l ;;

(* Available in OCaml since 4.01.00 - optimisable with "%apply" and "%revapply" *)
let (|>) x f = f x
;;
let (@@) f x = f x
;;



type ('a, 'b) union
  = Inl of 'a
  | Inr of 'b
;;

let sum f l =
  List.map f l |>
  List.fold_left (+) 0
;;

let r = Ulib.Text.of_latin1
;;

let iterate i n = Array.make n i |> Array.to_list
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

let span p l = (take_while p l, drop_while p l)
;;

let rec group_with p l =
  match l with
    | []    -> []
    | x::xs ->
        let (ys, zs) = span (p x) xs in
          (x::ys)::group_with p zs
;;

let from_string x = meta x
let sep x s = ws s ^ x
let path_sep = from_string "."

let tyvar (_, tv, _) = id Type_var (Ulib.Text.(^^^) (r"") tv)
let separate s = concat (from_string s)
let combine = flat

let lskips_t_to_output name =
  let stripped = Name.strip_lskip name in
  let rope = Name.to_rope stripped in
    Output.id Term_var rope
;;
