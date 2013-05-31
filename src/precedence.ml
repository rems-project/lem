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
open Typed_ast

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

type t = P_prefix
       | P_infix of int
       | P_infix_left of int
       | P_infix_right of int
       | P_special

let t_to_int = function
  | P_special _ -> -1
  | P_prefix -> 0
  | P_infix i -> i
  | P_infix_left i -> i
  | P_infix_right i -> i
  

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
  | P_prefix -> false
  | _ -> true

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
    (P_infix_right 1)
  else if string_match star s 0 then
    (P_infix_left 2)
  else if string_match plus s 0 then
    (P_infix_left 3)
  else if string_match cons s 0 then
    (P_infix_right 4)
  else if string_match at s 0 then
    (P_infix_right 5)
  else if string_match eq s 0 then
    (P_infix_left 6)
  else if string_match amp s 0 then
    (P_infix_right 7)
  else if string_match bar_bar s 0 then
    (P_infix_right 8)
  else if string_match imp s 0 then
    (P_infix_right 9)
  else
    P_prefix


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
    (P_infix_right 1)
  else if string_match star_ocaml s 0 then
    (P_infix_left 2)
  else if string_match plus_ocaml s 0 then
    (P_infix_left 3)
  else if string_match cons s 0 then
    (P_infix_right 4)
  else if string_match at s 0 then
    (P_infix_right 5)
  else if string_match eq_ocaml s 0 then
    (P_infix_left 6)
  else if string_match amp s 0 then
    (P_infix_right 7)
  else if string_match bar_bar s 0 then
    (P_infix_right 8)
  else
    P_prefix

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
    (P_infix_right 1)
  else if List.mem s ["@@"; "**"; "EXP"; "int_exp"] then
    (P_infix_right 2)
  else if List.mem s ["#<<"; "#>>"; ">>>"; ">>"; "<<"] then
    (P_infix_left 3)
  else if List.mem s ["MOD"; "%"] then
    (P_infix_left 4)
  else if List.mem s ["*,"] then
    (P_infix_right 5)
  else if List.mem s ["tint_mul"; "quot"; "/"; "//"; "\\"; "|+"; "CROSS"; "INTER"; "DIV"; "*"; "RINTER"] then
    (P_infix_left 6)
  else if List.mem s ["int_sub"; "tint_add"; "fcp_index"; "UNION"; "f_o"; "o_f"; "f_o_f"; "|++"; "DELETE"; "DIFF"; "-"; "+"; "RUNION"] then
    (P_infix_left 7)
  else if List.mem s ["###"; "===>"; "-->"; "::"; "INSERT"; "LEX"; "##"] then
    (P_infix_right 8)
  else if List.mem s ["+++"; "++"] then
    (P_infix_left 9)
  else if List.mem s ["int_divides"; ">=+"; "<+"; ">+"; "<=+"; "=="; "SUBMAP"; "<<="; "PSUBSET"; "SUBSET"; ">="; "<="; ">"; "<"; "RSUBSET"; "<>"] then
    (P_infix 10)
  else if List.mem s ["equiv_on"; "NOTIN"; "IN"] then
    (P_infix 11)
  else if List.mem s ["&&"; "~&&"; "/\\"] then
    (P_infix_right 12)
  else if List.mem s ["---"; "><"; "--"; "''"; "~??"; "??"] then
    (P_infix_right 13)
  else if List.mem s [":+"] then
    (P_infix_left 14)
  else if List.mem s ["=+"] then
    (P_infix 15)
  else if List.mem s [":>"] then
    (P_infix_left 16)
  else if List.mem s ["!!"; "~!!"; "\\/"] then
    (P_infix_right 17)
  else if List.mem s ["==>"] then
    (P_infix_right 18)
  else if List.mem s ["<=/=>"; "<=>"; "="] then
    (P_infix 19)
  else if List.mem s [":-"] then
    (P_infix 20)
  else
    P_prefix
    

let get_prec_isa s =
  let s = 
    match s with
      | Cons -> "#"
      | Op(s) -> s
  in
  (* 110 (isa prec) - map restric *)
  if List.mem s ["|`"] then 
    (P_infix_left 1)
  (* 100 *)
  else if List.mem s ["!"; "++"; "!!"] then 
    (P_infix_left 2)
  (* 95 - image and vimage ops *) 
  else if List.mem s ["`"; "-`"] then 
    (P_infix_right 3)
  (* 90 *)
  else if List.mem s ["BIT"] then 
    (P_infix_left 4)
  (* 80 *) 
  else if List.mem s ["<*>"; "\\<times>"] then 
    (P_infix_right 5)
  (* 70 *)
  else if List.mem s ["\\<inter>"; "div"; "mod"; "*"; "/"; "\\<sqinter>"] then 
    (P_infix_left 6)
  (* 70 - some ops from Imperative_HOL: noteq_array, noteq_ref *)
  else if List.mem s ["=!!=!"; "=!="] then
    (P_infix 6)
  (* 65 *)
  else if List.mem s ["\\<union>"; "-"; "+"; "\\<sqinter>"] then
    (P_infix_left 7)
  (* 65 *)
  else if List.mem s ["#"; "@"] then 
    (P_infix_right 7) (* Same precedence as union, but to the right, not to the left! *)
  (* 60 *)
  else if List.mem s ["\\<circ>>"; "\\<circ>\\<rightarrow>"] then 
    (P_infix_left 8)
  (* 55 *)
  else if List.mem s ["o"; "\\<circ>"; "o'_m"; "\\<circ>\\<^sub>m"; "<<"; ">>"; ">>>"] then
    (P_infix_left 9)
  (* 50 *)
  else if List.mem s ["=";"~=";"\\<noteq>";"udvd";"dvd"] then 
    (P_infix_left 10)
  (* 50 *)
  else if List.mem s [">=";">";"<";"<=";"\\<ge>";"\\<le>";"\\<sqsubseteq>";"\\<sqsubset>"] then 
    (P_infix 10)
  (* 35 *)
  else if List.mem s ["&";"\\<and>"] then 
    (P_infix_right 11)
  (* 30 *)
  else if List.mem s ["|";"\\<or>"] then 
    (P_infix_right 12)
  (* 25 *)
  else if List.mem s ["-->";"\\<longrightarrow>";"<->";"\\<longleftrightarrow>"] then 
    (P_infix_right 13)
  (* 20 - This is the product type * which is 'overloaded' Isabelle - what to do? *)
  (*
  else if List.mem s ["*"] then 
    (P_infix_right 13) *)
  (* 2 *) 
  else if List.mem s ["=="; "\\<equiv>"] then
    (P_infix_right 14)
  else 
    P_prefix


let needs_parens context t =
  match (context,t) with
    | (_,Atomic) -> false
    | (Delimited,_) -> false
    | (Field,_) -> true
    | ((App_right|Infix_right P_prefix|Infix_left P_prefix), _) -> true
    | (App_left, (App|Infix P_prefix)) -> false
    | (App_left,_) -> true
    | ((Infix_left _ | Infix_right _), (App|Infix P_prefix)) -> false
    | ((Infix_left _ | Infix_right _), Let) -> true
    | (Infix_left p1, Infix p2) ->
          if t_to_int p1 < t_to_int p2 then
            true
          else if t_to_int p1 = t_to_int p2 then
            match (p1, p2) with
              | (P_infix_left _, P_infix_left _) -> false 
              | _ -> true
          else
            false
    | (Infix_right p1, Infix p2) ->
          if t_to_int p1 < t_to_int p2 then
            true
          else if t_to_int p1 = t_to_int p2 then
            match (p1, p2) with
              | (P_infix_right _, P_infix_right _) -> false 
              | _ -> true
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


let get_prec target_opt env c =
  let l = Ast.Trans ("get_prec", None) in
  let c_descr = c_env_lookup l env.c_env c in

(* TODO: Use the taregt_rep
  let i = match Target.Targetmap.apply_opt c_descr.target_rep target_opt with
     | None -> resolve_ident_path c_id c_descr.const_binding
     | Some (CR_new_ident i) -> i
     | Some (CR_rename n) -> rename_ident (resolve_ident_path c_id c_descr.const_binding) n
     | Some (CR_inline _) -> (* TODO: handle inline here instead of macro *) assert false
*)
  
  let n = Path.get_name c_descr.const_binding in
  let p_fun = match target_opt with 
    | Some Target.Target_ocaml -> get_prec_ocaml
    | Some Target.Target_hol -> get_prec_hol
    | Some Target.Target_isa -> get_prec_isa
    | _ -> get_prec
  in
  p_fun (Op (Name.to_string n))
