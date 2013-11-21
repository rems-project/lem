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

let format_pos ff p = (
  Format.fprintf ff "File \"%s\", line %d, character %d:\n"
    p.Lexing.pos_fname p.Lexing.pos_lnum (p.Lexing.pos_cnum - p.Lexing.pos_bol);
  Format.pp_print_flush ff ())


let format_pos2 ff p1 p2 = (
  Format.fprintf ff "File \"%s\", line %d, character %d to line %d, character %d"
    p1.Lexing.pos_fname 
    p1.Lexing.pos_lnum (p1.Lexing.pos_cnum - p1.Lexing.pos_bol + 1)
    p2.Lexing.pos_lnum (p2.Lexing.pos_cnum - p2.Lexing.pos_bol);
  Format.pp_print_flush ff ()
)

(* reads the part between p1 and p2 from the file *)

let read_from_file_pos2 p1 p2 =
  let (s, e, multi) = if p1.Lexing.pos_lnum = p2.Lexing.pos_lnum then
                  (* everything in the same line, so really only read this small part*)
                  (p1.Lexing.pos_cnum, p2.Lexing.pos_cnum, None) 
               else (*multiline, so start reading at beginning of line *)
                  (p1.Lexing.pos_bol, p2.Lexing.pos_cnum, Some (p1.Lexing.pos_cnum - p1.Lexing.pos_bol)) in

  let ic = open_in p1.Lexing.pos_fname in
  let _ = seek_in ic s in
  let l = (e - s) in
  let buf = String.create l in
  let _ = input ic buf 0 l in
  let _ = match multi with None -> () | Some sk -> String.fill buf 0 sk ' ' in
  let _ = close_in ic in
  (buf, not (multi = None))

(* Destruct a location by splitting all the Ast.Trans strings except possibly the
   last one into a string list and keeping only the last location *)
let dest_loc (l : Ast.l) : (Ast.l * string list) = 
  let rec aux acc l = match l with
    | Ast.Trans(_, s, Some l') -> aux (s::acc) l'
    | _ -> (l, acc)
  in
  aux [] l

let rec format_loc_aux only_first ff l =
  let (l_org, mod_s) = dest_loc l in
  let _ = match l_org with
    | Ast.Unknown -> Format.fprintf ff "no location information available"
    | Ast.Range(p1,p2) -> format_pos2 ff p1 p2
    | Ast.Trans(_,s,_) -> Format.fprintf ff "code generated by: %s" s
  in
  if (not only_first) && (List.length mod_s > 0) then begin
    let mod_s' = String.concat ", " mod_s in
    let _ = Format.fprintf ff " processed by: %s" mod_s' in () 
  end else ()

let format_loc_source ff l = 
  match dest_loc l with 
  | (Ast.Range (p1, p2), _) -> 
    begin
      let (s, multi_line) = read_from_file_pos2 p1 p2 in
      if multi_line then 
        Format.fprintf ff "  original input:\n%s\n" s
      else
        Format.fprintf ff "  original input: \"%s\"\n" s
    end
  | _ -> ()

let format_loc only_first ff l =
 (format_loc_aux only_first ff l;
  Format.pp_print_newline ff ();
  Format.pp_print_flush ff ()
);;

let print_err_loc only_first l = 
   (format_loc only_first Format.err_formatter l)

let print_pos p = format_pos Format.std_formatter p
let print_err_pos p = format_pos Format.err_formatter p

let loc_to_string only_first l =
  let _ = Format.flush_str_formatter () in
  let _ = format_loc_aux only_first Format.str_formatter l in
  let s = Format.flush_str_formatter () in
  s

type pos_or_loc = Loc of Ast.l | Pos of Lexing.position

let print_err_internal fatal verb_loc only_first p_l m1 m2 =
  let _ = (match p_l with Pos p -> print_err_pos p | Loc l -> print_err_loc only_first l) in
  let m12 = if String.length m2 = 0 then "" else ": " in
  Format.eprintf "  %s%s%s\n" m1 m12 m2;
  if verb_loc then (match p_l with Loc l -> format_loc_source Format.err_formatter l; Format.pp_print_newline Format.err_formatter (); | _ -> ());
  Format.pp_print_flush Format.err_formatter ();
  if fatal then (exit 1) else ()

let print_err fatal verb_loc only_first l m1 m2 =
  print_err_internal fatal verb_loc only_first (Loc l) m1 m2


type error = 
  | Err_general of bool * Ast.l * string
  | Err_unreachable of Ast.l * string
  | Err_todo of bool * Ast.l * string
  | Err_trans of Ast.l * string
  | Err_trans_header of Ast.l * string
  | Err_syntax of Lexing.position * string
  | Err_syntax_locn of Ast.l * string
  | Err_lex of Lexing.position * char
  | Err_type of Ast.l * string
  | Err_internal of Ast.l * string
  | Err_rename of Ast.l * string
  | Err_cyclic_build of string 
  | Err_cyclic_inline of Ast.l * string * string
  | Err_resolve_dependency of Ast.l * string list * string 
  | Err_reorder_dependency of Ast.l * string
  | Err_fancy_pattern_constant of Ast.l * string 

let dest_err = function
  | Err_general (b, l, m) -> ("Error", b, Loc l, m)
  | Err_unreachable (l, m) -> ("Unreachable code", true, Loc l, m)
  | Err_todo (b, l, m) -> ("LEM internal error", b, Loc l, "unimplemented feature "^m)
  | Err_trans (l, m) -> ("Translation error", false, Loc l, m)
  | Err_syntax (p, m) -> ("Syntax error", false, Pos p, m)
  | Err_syntax_locn (l, m) -> ("Syntax error", false, Loc l, m)
  | Err_lex (p, c) -> ("Lexical error", false, Pos p, "unknown character "^(String.make 1 c))
  | Err_trans_header (l, m) -> ("Header translation error", false,  Loc l, m)
  | Err_internal (l, m) -> ("LEM internal error", false, Loc l, m)
  | Err_rename (l, m) -> ("Renaming error", false, Loc l, m)
  | Err_type (l, m) -> ("Type error", false, Loc l, m)
  | Err_fancy_pattern_constant (l, m) -> ("Unsupported pattern", false, Loc l, m)
  | Err_cyclic_build m -> ("Circular build detected", false, Loc Ast.Unknown, "module '" ^ m ^ "' depends on itself")
  | Err_cyclic_inline (l, targ, c) -> ("Circular target definition", false, Loc l, "the definition of " ^ c ^ " for target " ^ targ ^ " depends on itself")
  | Err_resolve_dependency (l, dirs, m) -> ("Unknown dependency", false, Loc l, ("could not find module '"^m^"' in directories " ^ (String.concat ", " (List.map (fun s -> "'" ^ s ^ "'") dirs))))
  | Err_reorder_dependency (l, m) -> ("Reordering dependency", false, Loc l, ("module '"^m^"' is needed earlier, but it reordering is not allowed"))

exception Fatal_error of error

(* Abbreviations for the very common cases *)
let err_todo b l m = Fatal_error (Err_todo (b, l, m))
let err_unreachable l m = Fatal_error (Err_unreachable (l, m))
let err_general b l m = Fatal_error (Err_general (b, l, m))

let err_type l m = Fatal_error (Err_type (l, m))

let err_type_pp l msg pp n =
  let pp ppf = Format.fprintf ppf "%s: %a" msg pp n in
  err_type l (Pp.pp_to_string pp)

let report_error e = 
  if Printexc.backtrace_status ()
  then Printexc.print_backtrace stderr;
  let (m1, verb_pos, pos_l, m2) = dest_err e in
  (print_err_internal true verb_pos false pos_l m1 m2; exit 1)


(******************************************************************************)
(* Debuging                                                                   *)
(******************************************************************************)

let debug_flag = ref true

let print_debug s =
  if (not !debug_flag) then () else
  (Format.eprintf "DEBUG: %s\n\n" s;
   Format.pp_print_flush Format.err_formatter ())

