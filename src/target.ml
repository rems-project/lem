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

let r = Ulib.Text.of_latin1

type non_ident_target = 
  | Target_hol
  | Target_ocaml
  | Target_isa
  | Target_coq
  | Target_tex
  | Target_html
  | Target_lem

type target =
  | Target_no_ident of non_ident_target 
  | Target_ident

let all_targets_list = [
  Target_ocaml;
  Target_lem; 
  Target_hol; 
  Target_isa; 
  Target_coq; 
  Target_tex; 
  Target_html;] 

let all_targets_only_exec_list = [
  Target_ocaml
] 

let ast_target_to_target t = match t with
  | Ast.Target_hol   _ -> Target_hol 
  | Ast.Target_ocaml _ -> Target_ocaml 
  | Ast.Target_isa   _ -> Target_isa
  | Ast.Target_coq   _ -> Target_coq
  | Ast.Target_tex   _ -> Target_tex
  | Ast.Target_html  _ -> Target_html
  | Ast.Target_lem   _ -> Target_lem

let target_to_ast_target t = match t with
  | Target_hol   -> Ast.Target_hol None
  | Target_ocaml -> Ast.Target_ocaml None
  | Target_isa   -> Ast.Target_isa None
  | Target_coq   -> Ast.Target_coq None
  | Target_tex   -> Ast.Target_tex None
  | Target_html  -> Ast.Target_html None
  | Target_lem   -> Ast.Target_lem None

let target_compare = Pervasives.compare

let ast_target_to_int = function
  | Ast.Target_lem _   -> 7
  | Ast.Target_hol _   -> 6
  | Ast.Target_ocaml _ -> 5
  | Ast.Target_isa _   -> 4
  | Ast.Target_coq _   -> 3
  | Ast.Target_tex _   -> 2
  | Ast.Target_html _  -> 1

let ast_target_compare x y = Pervasives.compare (ast_target_to_int x) (ast_target_to_int y)

module Targetmap = struct 

  (* include finite maps *)
  include Finite_map.Fmap_map(
    struct 
      type t = non_ident_target
      let compare = target_compare
    end
  )

  let apply_target m targ = 
    match targ with
      | Target_ident -> None (* No entry for identity backend *)
      | Target_no_ident t -> apply m t

  let insert_target m (targ, v) = 
    match targ with
      | Target_ident -> m
      | Target_no_ident t -> insert m (t, v)

end

module Targetset = Set.Make(
struct 
  type t = non_ident_target
  let compare = target_compare
end)

let all_targets = List.fold_right Targetset.add all_targets_list Targetset.empty

let all_targets_non_explicit = Targetset.remove Target_lem all_targets
let all_targets_only_exec = List.fold_right Targetset.add all_targets_only_exec_list Targetset.empty

let non_ident_target_to_string = function
  | Target_hol -> "hol"
  | Target_ocaml -> "ocaml"
  | Target_isa -> "isabelle"
  | Target_coq -> "coq"
  | Target_tex -> "tex"
  | Target_html -> "html"
  | Target_lem -> "lem"

let target_to_string = function
  | Target_ident -> "ident"
  | Target_no_ident t -> non_ident_target_to_string t

let target_to_output t = 
  let open Output in
    let a = Output.Target in
    match t with
      | Ast.Target_hol(s) -> ws s ^ id a (r"hol")
      | Ast.Target_ocaml(s) -> ws s ^ id a (r"ocaml")
      | Ast.Target_isa(s) -> ws s ^ id a (r"isabelle")
      | Ast.Target_coq(s) -> ws s ^ id a (r"coq")
      | Ast.Target_tex(s) -> ws s ^ id a (r"tex")
      | Ast.Target_html(s) -> ws s ^ id a (r"html")
      | Ast.Target_lem(s) -> ws s ^ id a (r"lem")

let non_ident_target_to_mname = function
  | Target_hol -> Name.from_rope (r"Hol")
  | Target_ocaml -> Name.from_rope (r"Ocaml")
  | Target_isa -> Name.from_rope (r"Isabelle")
  | Target_coq -> Name.from_rope (r"Coq")
  | Target_tex -> Name.from_rope (r"Tex")
  | Target_html -> Name.from_rope (r"Html")
  | Target_lem -> Name.from_rope (r"Lem")


let is_human_target = function
    Target_ident -> true
  | Target_no_ident Target_isa   -> false
  | Target_no_ident Target_hol   -> false
  | Target_no_ident Target_coq   -> false
  | Target_no_ident Target_ocaml -> false
  | Target_no_ident Target_html  -> true
  | Target_no_ident Target_tex   -> true
  | Target_no_ident Target_lem   -> true
  
let is_tex_target targ =
	match targ with
		| Target_no_ident Target_tex -> true
		| _ -> false

let suppress_targets current_target tex_flag =
	match current_target with
		| Target_no_ident Target_tex -> tex_flag
		| _ -> false
;;

let dest_human_target = function
    Target_ident -> None
  | Target_no_ident t ->  if is_human_target (Target_no_ident t) then None else Some t
