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

open Coq_backend_utils

type 'a parser = char list -> ('a * char list) list
;;

let char_list_of_string s =
  let len = String.length s in
  let rec aux n =
    if n < len then
      s.[n] :: aux (n + 1)
    else
      []
  in
    aux 0
;;

let iteri (i : int -> 'a -> unit) (l : 'a list) =
  let rec aux counter i l =
    match l with
      | [] -> ()
      | hd::tl ->
          let _ = i counter hd in
            aux (counter + 1) i tl
  in
    aux 0 i l
;;

let string_of_char_list (cs : char list) : string =
  let length = List.length cs in
  let buffer = String.create length in
  let _ = iteri (fun c -> fun x -> String.set buffer c x) cs in
    buffer
;;

(* Monadic interface *)

let return x =
  fun y -> [(x, y)]
;;

let (>>=) f g =
  fun x ->
    let frst = f x in
      List.concat (List.map (fun (a, x') -> (g a) x') frst)
;;

(* Some simple parsers. *)

(** A parser that always fails.
 *)
let fail : 'a parser =
  fun _ -> []
;;

(** A parser that succeeds on empty input (i.e. the end of file) and
    fails when there is more input to consume.
 *)
let eof : unit parser =
  function
    | [] -> [(), []]
    | _  -> []
;;

(** A parser that take a predicate on characters, succeeding if the
    predicate holds on the first character to be consumed in the input
    stream, failing otherwise.
 *)
let predicate p =
  function
    | hd::tl ->
      if p hd then
        [(hd, tl)]
      else
        []
    | [] -> []
;;

(** Parallel composition of parsers.
 *)
let (++) f g =
  fun x ->
    f x @ g x
;;

(** A specialisation of [(++)] above.  If [(++)] fails, then so does
    [(+?+)], otherwise [(+?+)] returns the first results of [(++)].)
 *)
let (+?+) f g =
  fun x ->
    match (f ++ g) x with
      | [] -> []
      | hd::_ -> [hd]
;;

(** A pair of higher-order parsers.
      [many] applies [p] repeatedly,
      [many1] applies [p] repeatedly, ensuring it succeeds at least once.
 *)
let rec many (p : 'a parser) =
  many1 p +?+ return []
    and many1 p =
  p      >>= fun a ->
  many p >>= fun b ->
  return (a::b)
;;

(** A higher-order parser.  Applies [p] to the input [i] times.
 *)
let rec repeat i p =
  if i = 0 then
    return []
  else
    p                >>= fun a ->
    repeat (i - 1) p >>= fun b ->
    return (a::b)
;;

(** A pair of higher-order parsers.
      [sep_by] parses input with [p] using [many], separating occurrences with [s],
      [sep_by1] parses input with [p] using [many1], separating occurrences with [s].
 *)
let rec sep_by p s =
  sep_by1 p s +?+ return []
and sep_by1 p s =
  p                       >>= fun a ->
  many (s >>= fun _ -> p) >>= fun b ->
  return (a::b)
;;

let one_of l =
  predicate (fun x -> List.mem x l)
;;


(* More specialised parsers. *)

(** Parses a character [c], failing if input stream does not have
    [c] as its head.
 *)
let char_exact (c : char) = 
  predicate (fun x -> x = c)
;;

(** Parses a string [s], failing if the initial characters in the
    input stream do not correspond to [s].
 *)
let string_exact s =
  let string_exact' s =
    let cs = char_list_of_string s in
    let rec aux =
      function
        | []    -> return []
        | x::xs ->
            char_exact x >>= fun x ->
            aux xs       >>= fun xs ->
            return (x :: xs)
    in
      aux cs
  in
    string_exact' s >>= fun r ->
    return (string_of_char_list r)
;;

(** Parses an int [i], failing if the initial characters in the
    input stream do not correspond to [i].
 *)
let int_exact i =
  string_exact (string_of_int i)
;;

(** Parses a boolean [b], failing if the initial characters in the
    input stream do not correspond to [b].
 *)
let bool_exact b =
  string_exact (string_of_bool b)
;;

let digit =
  one_of ['0'; '1'; '2'; '3'; '4'; '5'; '6'; '7'; '8'; '9'] >>= fun d ->
  let s = String.make 1 d in
  return (int_of_string s)
;;

let digits =
  many1 digit >>= fun ds ->
  let r = Util.list_mapi (fun d -> fun e -> e * (10 * List.length ds - d)) ds in
  let r = List.fold_right (+) r 0 in
    return r
;;

let whitespace =
  one_of [' '; '\t'; '\r'; '\n'] >>= fun c ->
  return (String.make 1 c)
;;

let whitespace1 =
  many1 whitespace >>= fun w ->
  return (List.fold_right (^) w "") 
;;

(* Performing parses. *)

type 'a parse_result
  = Yes of 'a
  | No of string
;;

let parse input parser =
  let chars = char_list_of_string input in
    match parser chars with
      | []            -> No ("Parsing failed on input " ^ input)
      | (r, rest)::tl -> Yes r
;;

let parse_and_print input parser printer =
  match parse input parser with
    | Yes r -> print_endline (printer r)
    | No  e -> print_endline e
;;
