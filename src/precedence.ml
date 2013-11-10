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
  
let ast_fixity_decl_to_t = function
 | Ast.Fixity_right_assoc   (_, i) -> P_infix_right i
 | Ast.Fixity_left_assoc    (_, i) -> P_infix_left i
 | Ast.Fixity_non_assoc     (_, i) -> P_infix i
 | Ast.Fixity_default_assoc        -> P_infix 0


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
  | P_special -> false
  | _ -> true

let oper_char = "[-!$%&*+./:<=>?@^|~]"
let star_star = regexp (Printf.sprintf "^[*][*]%s*\\|lsl\\|lsr\\|asr$" oper_char)
let star = regexp (Printf.sprintf "^\\([*/%%]%s*\\|inter\\|mod\\|land\\|lor\\|lxor\\)$" oper_char)
let plus = regexp (Printf.sprintf "^\\([+-]%s*\\|union\\)$" oper_char)
let cons = regexp "^::$"
let at = regexp (Printf.sprintf "^[@^]%s*$" oper_char)
let eq = regexp (Printf.sprintf "^\\([=<>|&$]%s*\\|IN\\|NIN\\|MEM\\|subset\\|[\\]\\)$" oper_char)
let amp = regexp "^&&$"
let bar_bar = regexp "^||$"
let imp = regexp "^-->$"

let get_ident_prec s = 
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


let rec get_prec targ env c =
  let l = Ast.Trans (false, "get_prec", None) in
  let c_descr = c_env_lookup l env.c_env c in

  match targ with
    | Target.Target_ident -> (* The precedences for the identity backend are hardcoded. *)
        get_ident_prec (Op (Name.to_string (Path.get_name c_descr.const_binding)))
    | Target.Target_no_ident targ' -> (* precedences for real targets are stored in the constant description *)
      begin
        match Target.Targetmap.apply c_descr.target_rep targ' with
         | Some (CR_infix (_, _, fixity, _)) -> ast_fixity_decl_to_t fixity
         | Some (CR_special _) -> P_special (* TODO: Thomas T.: uncertain, whether P_prefix would be better here, but it should not matter much I hope *)
         | Some (CR_inline (_, _, [], e)) -> get_prec_exp targ env e
         | Some (CR_simple (_, _, [], e)) -> get_prec_exp targ env e
         | Some _ -> P_prefix
         | None ->
            get_ident_prec (Op (Name.to_string (Path.get_name c_descr.const_binding)))
      end

and get_prec_exp targ env e =
  let module C = Exps_in_context(struct let env_opt = Some env;; let avoid = None end) in
  match C.exp_to_term e with
    | Constant id -> get_prec targ env id.Types.descr
    | Paren (_, e, _) -> get_prec_exp targ env e
    | Typed (_, e, _, _, _) -> get_prec_exp targ env e
    | _ -> P_prefix
  
