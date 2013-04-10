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

(** the precedence model for the backends *)

open Str

(* Lem source can have 3 kinds of expressions involving infixes:
 * x + y
 * (+) x y
 * M.(+) x y
 *
 * For x + y we can convert to 
 * (+) x y if + is infix in the target or + x y if it isn't
 *
 * For (+) x y we can convert to
 * x + y if + is infix in the target or + x y if it isn't
 *
 * For M.(+) x y we must convert to
 * M.+ if + isn't infix in the target
 *
 *)


type op = Cons | Op of string

type assoc = | Right | Left | Nonassoc

type t = int * assoc

type pat_context =
  | Plist
  | Pas_left
  | Pcons_left
  | Pcons_right
  | Pdelimited

type pat_kind =
  | Papp
  | Pas
  | Padd
  | Pcons
  | Patomic

type context = 
  | Field
  | App_right
  | App_left
  | Infix_left of t
  | Infix_right of t
  | Delimited

type exp_kind =
  | App
  | Infix of t
  | Let
  | Atomic

let is_infix = function
  | (0,_) -> false
  | _ -> true

let not_infix = (0,Left)

let oper_char = "[-!$%&*+./:<=>?@^|~]"
let star_star = regexp (Printf.sprintf "^[*][*]%s*\\|lsl\\|lsr\\|asr$" oper_char)
let star = regexp (Printf.sprintf "^\\([*/%%]%s*\\|inter\\|mod\\|land\\|lor\\|lxor\\)$" oper_char)
let plus = regexp (Printf.sprintf "^\\([+-]%s*\\|union\\)$" oper_char)
let cons = regexp "^::$"
let at = regexp (Printf.sprintf "^[@^]%s*$" oper_char)
let eq = regexp (Printf.sprintf "^\\([=<>|&$]%s*\\|IN\\|MEM\\|subset\\|[\\]\\)$" oper_char)
let amp = regexp "^&&$"
let bar_bar = regexp "^||$"
let imp = regexp "^-->$"

let get_prec s = 
  let s = 
    match s with
      | Cons -> "::"
      | Op(s) -> s
  in
  if string_match star_star s 0 then
    (1,Right)
  else if string_match star s 0 then
    (2,Left)
  else if string_match plus s 0 then
    (3,Left)
  else if string_match cons s 0 then
    (4,Right)
  else if string_match at s 0 then
    (5,Right)
  else if string_match eq s 0 then
    (6,Left)
  else if string_match amp s 0 then
    (7,Right)
  else if string_match bar_bar s 0 then
    (8,Right)
  else if string_match imp s 0 then
    (9,Right)
  else
    (0,Left)


let star_ocaml = regexp (Printf.sprintf "^\\([*/%%]%s*\\|mod\\|land\\|lor\\|lxor\\)$" oper_char)
let plus_ocaml = regexp (Printf.sprintf "^\\([+-]%s*\\)$" oper_char)
let eq_ocaml = regexp (Printf.sprintf "^\\([=<>|&$]%s*\\)$" oper_char)

let get_prec_ocaml s = 
  let s = 
    match s with
      | Cons -> "::"
      | Op(s) -> s
  in
  if string_match star_star s 0 then
    (1,Right)
  else if string_match star_ocaml s 0 then
    (2,Left)
  else if string_match plus_ocaml s 0 then
    (3,Left)
  else if string_match cons s 0 then
    (4,Right)
  else if string_match at s 0 then
    (5,Right)
  else if string_match eq_ocaml s 0 then
    (6,Left)
  else if string_match amp s 0 then
    (7,Right)
  else if string_match bar_bar s 0 then
    (8,Right)
  else
    (0,Left)

let hol_important_constants = 
  ["let"; "in"; "and"; "\\"; "."; ";"; "=>"; "|"; "||"; ":"; ":="; "with";
   "updated_by"; "case"; "of"; "LEAST"; "?!"; "?"; "!"; "@"; "::"; "->"; ",";
   "if"; "then"; "else"; "with"; "/\\"; "\\/"; "T"; "F"; "|>"; "<|"; "==>";
   "=";] 

let get_prec_hol s = 
  let s = 
    match s with
      | Cons -> "::"
      | Op(s) -> s
  in
(*
Field
univ
^= ^* ^+
Application and '
& - ~
 *)
  if List.mem s ["O"; "o"] then
    (1,Right)
  else if List.mem s ["@@"; "**"; "EXP"; "int_exp"] then
    (2,Right)
  else if List.mem s ["#<<"; "#>>"; ">>>"; ">>"; "<<"] then
    (3,Left)
  else if List.mem s ["MOD"; "%"] then
    (4,Left)
  else if List.mem s ["*,"] then
    (5,Right)
  else if List.mem s ["tint_mul"; "quot"; "/"; "//"; "\\"; "|+"; "CROSS"; "INTER"; "DIV"; "*"; "RINTER"] then
    (6,Left)
  else if List.mem s ["int_sub"; "tint_add"; "fcp_index"; "UNION"; "f_o"; "o_f"; "f_o_f"; "|++"; "DELETE"; "DIFF"; "-"; "+"; "RUNION"] then
    (7,Left)
  else if List.mem s ["###"; "===>"; "-->"; "::"; "INSERT"; "LEX"; "##"] then
    (8,Right)
  else if List.mem s ["+++"; "++"] then
    (9,Left)
  else if List.mem s ["int_divides"; ">=+"; "<+"; ">+"; "<=+"; "=="; "SUBMAP"; "<<="; "PSUBSET"; "SUBSET"; ">="; "<="; ">"; "<"; "RSUBSET"; "<>"] then
    (10,Nonassoc)
  else if List.mem s ["equiv_on"; "NOTIN"; "IN"] then
    (11,Nonassoc)
  else if List.mem s ["&&"; "~&&"; "/\\"] then
    (12,Right)
  else if List.mem s ["---"; "><"; "--"; "''"; "~??"; "??"] then
    (13,Right)
  else if List.mem s [":+"] then
    (14,Left)
  else if List.mem s ["=+"] then
    (15,Nonassoc)
  else if List.mem s [":>"] then
    (16,Left)
  else if List.mem s ["!!"; "~!!"; "\\/"] then
    (17,Right)
  else if List.mem s ["==>"] then
    (18,Right)
  else if List.mem s ["<=/=>"; "<=>"; "="] then
    (19,Nonassoc)
  else if List.mem s [":-"] then
    (20,Nonassoc)
  else
    (0,Left)
    

let get_prec_isa s =
  let s = 
    match s with
      | Cons -> "#"
      | Op(s) -> s
  in
  (* 110 (isa prec) - map restric *)
  if List.mem s ["|`"] then 
    (1,Left)
  (* 100 *)
  else if List.mem s ["!"; "++"; "!!"] then 
    (2,Left)
  (* 95 - image and vimage ops *) 
  else if List.mem s ["`"; "-`"] then 
    (3, Right)
  (* 90 *)
  else if List.mem s ["BIT"] then 
    (4,Left)
  (* 80 *) 
  else if List.mem s ["<*>"; "\\<times>"] then 
    (5, Right)
  (* 70 *)
  else if List.mem s ["\\<inter>"; "div"; "mod"; "*"; "/"; "\\<sqinter>"] then 
    (6, Left)
  (* 70 - some ops from Imperative_HOL: noteq_array, noteq_ref *)
  else if List.mem s ["=!!=!"; "=!="] then
    (6, Nonassoc) 
  (* 65 *)
  else if List.mem s ["\\<union>"; "-"; "+"; "\\<sqinter>"] then
    (7, Left)
  (* 65 *)
  else if List.mem s ["#"; "@"] then 
    (7, Right)   (* Same precedence as union, but to the right, not to the left! *)
  (* 60 *)
  else if List.mem s ["\\<circ>>"; "\\<circ>\\<rightarrow>"] then 
    (8, Left)
  (* 55 *)
  else if List.mem s ["o"; "\\<circ>"; "o'_m"; "\\<circ>\\<^sub>m"; "<<"; ">>"; ">>>"] then
    (9, Left)
  (* 50 *)
  else if List.mem s ["=";"~=";"\\<noteq>";"udvd";"dvd"] then 
    (10, Left)
  (* 50 *)
  else if List.mem s [">=";">";"<";"<=";"\\<ge>";"\\<le>";"\\<sqsubseteq>";"\\<sqsubset>"] then 
    (10, Nonassoc)
  (* 35 *)
  else if List.mem s ["&";"\\<and>"] then 
    (11, Right)
  (* 30 *)
  else if List.mem s ["|";"\\<or>"] then 
    (12, Right)
  (* 25 *)
  else if List.mem s ["-->";"\\<longrightarrow>";"<->";"\\<longleftrightarrow>"] then 
    (13, Right)
  (* 20 - This is the product type * which is 'overloaded' Isabelle - what to do? *)
  (*
  else if List.mem s ["*"] then 
    (13, Right) *)
  (* 2 *) 
  else if List.mem s ["=="; "\\<equiv>"] then
    (14, Right)
  else 
    (0, Left)


let needs_parens context t =
  match (context,t) with
    | (_,Atomic) -> false
    | (Delimited,_) -> false
    | (Field,_) -> true
    | ((App_right|Infix_right(0,_)|Infix_left(0,_)), _) -> true
    | (App_left, (App|Infix(0,_))) -> false
    | (App_left,_) -> true
    | ((Infix_left _ | Infix_right _), (App|Infix(0,_))) -> false
    | ((Infix_left _ | Infix_right _), Let) -> true
    | (Infix_left((p1,a1)), Infix((p2,a2))) ->
          if p1 < p2 then
            true
          else if p1 = p2 then
            not (a1 = Left && a2 = Left)
          else
            false
    | (Infix_right((p1,a1)), Infix((p2,a2))) ->
          if p1 < p2 then
            true
          else if p1 = p2 then
            not (a1 = Right && a2 = Right)
          else
            false

let pat_needs_parens context t =
  match (context,t) with
    | (_,Patomic) -> false
    | (Pdelimited,_) -> false
    | (Plist,_) -> true
    | (Pas_left, _) -> false
    | (Pcons_left,Pcons) -> true
    | (Pcons_left,_) -> false
    | (Pcons_right,Pas) -> true
    | (Pcons_right,_) -> false

