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

open Reporting_basic

type warn_source = 
  | Warn_source_exp of Typed_ast.exp
  | Warn_source_def of Typed_ast.def
  | Warn_source_unkown

let warn_source_to_locn = function
    Warn_source_exp e -> Typed_ast.exp_to_locn e
  | Warn_source_def (_, l) -> l
  | Warn_source_unkown -> Ast.Unknown
  
type warning = 
  | Warn_general of bool * Ast.l * string
  | Warn_rename of Ast.l * string * (string * Ast.l) option * string * Typed_ast.target option
  | Warn_pattern_compilation_failed of Ast.l * Typed_ast.pat list * warn_source
  | Warn_pattern_not_exhaustive of Ast.l * Typed_ast.pat list list
  | Warn_def_not_exhaustive of Ast.l * string * Typed_ast.pat list list
  | Warn_pattern_redundant of Ast.l * (int * Typed_ast.pat) list * Typed_ast.exp
  | Warn_def_redundant of Ast.l * string * (int * Typed_ast.pat) list * Typed_ast.def
  | Warn_pattern_needs_compilation of Ast.l * Typed_ast.target option * Typed_ast.exp * Typed_ast.exp
  | Warn_unused_vars of Ast.l * string list * warn_source
  | Warn_fun_clauses_resorted of Ast.l * Typed_ast.target option * string list * Typed_ast.def
  | Warn_record_resorted of Ast.l * Typed_ast.exp
  | Warn_no_decidable_equality of Ast.l * string

let warn_source_to_string exp def ws =
  match ws with 
      Warn_source_exp e -> Some ("expression", Ulib.Text.to_string (exp e))
    | Warn_source_def d -> Some ("definition", Ulib.Text.to_string (def d))
    | Warn_source_unkown -> None

(* construct the appropriate output of a warning. The result is a triple (b, l, m) stating
   b: print the text at source location in verbose mode?
   l: the source location
   m: the message to display
*)
let dest_warning (env : Typed_ast.env) (verbose: bool) (w : warning) : (bool * Ast.l * string) option = 
  let module B = Backend.Make(struct
    let avoid = (false, (fun _ -> true), Name.fresh);;
    let env = env
  end) in
  match w with
  | Warn_general (b, l, m) -> Some (b, l, m)

  | Warn_rename (l, n_org, n_via_opt, n_new, targ) ->
     let target_s = (Typed_ast.target_opt_to_string targ) in
     let via_s = (Util.option_default "" (Util.option_map (fun (n, l') -> "\n  via '"^n^"' at " ^
                  loc_to_string true l') n_via_opt)) in
     let m = Format.sprintf "renaming '%s' to '%s' for target %s%s" n_org n_new target_s via_s in
     Some (false, l, m)

  | Warn_pattern_compilation_failed (l, pL, ws) -> 
      let psL = List.map (fun p -> "'" ^ Ulib.Text.to_string (B.ident_pat p) ^ "'") pL in
      let ps = String.concat ", " psL in
      let m = Format.sprintf "could not compile the following list of patterns: %s" ps in
      let m' = if not verbose then "" else
          (match warn_source_to_string B.ident_exp B.ident_def ws with None -> "" | Some (l, s) -> Format.sprintf "\n  in the following %s\n    %s\n" l s)
      in
      Some (true, l, m ^ m')

  | Warn_pattern_not_exhaustive (l, pLL) -> 
      let pL_to_string pL = String.concat " " (List.map (fun p -> Ulib.Text.to_string (B.ident_pat p)) pL) in
      let ps = String.concat ", " (List.map (fun pL -> "'" ^ pL_to_string pL ^ "'") pLL) in     
      Some (true, l, "pattern-matching is not exhaustive\n  missing patterns " ^ ps)

  | Warn_def_not_exhaustive (l, n, pLL) -> 
      let pL_to_string pL = String.concat " " (List.map (fun p -> Ulib.Text.to_string (B.ident_pat p)) pL) in
      let ps = String.concat ", " (List.map (fun pL -> "'" ^ pL_to_string pL ^ "'") pLL) in     
      Some (true, l, "function '"^n^"' is defined by non-exhaustive pattern-matching\n  missing patterns " ^ ps)

  | Warn_pattern_redundant (l, rL, e) -> 
      let pat_label = if List.length rL > 1 then "patterns" else "pattern" in
      let psL = List.map (fun (_,p) -> "'" ^ Ulib.Text.to_string (B.ident_pat p) ^ "'") rL in
      let ps = String.concat ", " psL in
      let m = Format.sprintf "redundant %s: %s" pat_label ps in
      Some (true, l, m)

  | Warn_def_redundant (l, n, rL, d) ->  
      let pat_label = if List.length rL > 1 then "patterns" else "pattern" in
      let psL = List.map (fun (_,p) -> "'" ^ Ulib.Text.to_string (B.ident_pat p) ^ "'") rL in
      let ps = String.concat ", " psL in
      let m = Format.sprintf "redundant %s in definition of function '%s': %s" n pat_label ps in
      Some (true, l, m)

  | Warn_pattern_needs_compilation (l, targ, e_old, e_new) -> 
      let target_s = Typed_ast.target_opt_to_string targ in
      let m_basic = "pattern compilation used for target " ^ target_s in
      let m_verb = if not verbose then "" else begin
        let e_old_s = Ulib.Text.to_string (B.ident_exp e_old) in
        let e_new_s = Ulib.Text.to_string (B.ident_exp e_new) in
        Format.sprintf "\n  the expression\n    %s\n  was compiled to\n    %s" e_old_s e_new_s
      end in
      let m = m_basic ^ m_verb in
      Some (true, l, m)

  | Warn_unused_vars (l, sl, ws) -> 
      let var_label = if List.length sl > 1 then "variables" else "variable" in
      let vsL = List.map (fun s -> ("'" ^ s ^ "'")) sl in
      let vs = String.concat ", " vsL in
      let m = Format.sprintf "unused %s: %s" var_label vs in
      Some (true, l, m)

  | Warn_fun_clauses_resorted (l, targ, nl, d) -> 
      let fun_label = if List.length nl > 1 then "functions " else "function " in
      let fsL = List.map (fun s -> ("'" ^ s ^ "'")) nl in
      let fs = String.concat ", " fsL in
      let target_s = Typed_ast.target_opt_to_string targ in
      let m : string = Format.sprintf "function definition clauses of %s %s reordered for target %s" fun_label fs target_s in
      Some (false, l, m)

  | Warn_record_resorted (l, e) -> 
      let m : string = "record fields reordered" in
      Some (true, l, m)

  | Warn_no_decidable_equality (l, n) -> 
      let m : string = "type '" ^ n ^ "' does not have a decidable equality" in
      Some (true, l, m)

(* Command line options that effect warnings *)

type warn_level = Level_Ignore | Level_Warn | Level_Warn_Verbose | Level_Error

let get_default_warn_level = function 
    []      -> None
  | [r]     -> Some (!r)
  | (r::rs) -> let wl = !r in if (List.for_all (fun r' -> !r' = wl) rs) then Some wl else None

(* define one reference per warning type *)
let warn_ref_general          = ref Level_Warn;;
let warn_ref_rename           = ref Level_Warn;;
let warn_ref_pat_fail         = ref Level_Warn;;
let warn_ref_pat_exh          = ref Level_Warn;;
let warn_ref_pat_red          = ref Level_Warn;;
let warn_ref_def_exh          = ref Level_Warn;;
let warn_ref_def_red          = ref Level_Warn;;
let warn_ref_pat_comp         = ref Level_Warn;;
let warn_ref_unused_vars      = ref Level_Warn;;
let warn_ref_fun_resort       = ref Level_Warn;;
let warn_ref_rec_resort       = ref Level_Warn;;
let warn_ref_no_decidable_eq  = ref Level_Warn;;

(* a list of all these references *)
let warn_refL = [
  warn_ref_rename; warn_ref_pat_fail; warn_ref_pat_exh; warn_ref_pat_red; warn_ref_def_exh; 
  warn_ref_def_red; warn_ref_pat_comp; warn_ref_unused_vars; warn_ref_general; 
  warn_ref_fun_resort; warn_ref_rec_resort; warn_ref_no_decidable_eq
]

(* map a warning to it's reference *)
let warn_level = function
  | Warn_general _ ->                           !warn_ref_general
  | Warn_rename _ ->                            !warn_ref_rename
  | Warn_pattern_compilation_failed _ ->        !warn_ref_pat_fail
  | Warn_pattern_not_exhaustive _ ->            !warn_ref_pat_exh
  | Warn_pattern_redundant _ ->                 !warn_ref_pat_red
  | Warn_def_not_exhaustive _ ->                !warn_ref_def_exh
  | Warn_def_redundant _ ->                     !warn_ref_def_red
  | Warn_pattern_needs_compilation _ ->         !warn_ref_pat_comp
  | Warn_unused_vars _ ->                       !warn_ref_unused_vars
  | Warn_fun_clauses_resorted _ ->              !warn_ref_fun_resort
  | Warn_record_resorted _ ->                   !warn_ref_rec_resort
  | Warn_no_decidable_equality _ ->             !warn_ref_no_decidable_eq

let ignore_pat_compile_warnings () = (warn_ref_pat_comp := Level_Ignore)

(* A list of the option, the entries consists of
   - "name of argument", 
   - reference to modify, 
   - doc string

   This is the list to modify in order to get the command line options working
*)

let warn_opts_aux = [
   ("unused_vars", [warn_ref_unused_vars],                     "unused variables");
   ("pat_fail",    [warn_ref_pat_fail],                        "failed pattern compilation");
   ("pat_exh",     [warn_ref_pat_exh; warn_ref_def_exh],       "non-exhaustive pattern matches");
   ("pat_red",     [warn_ref_pat_red; warn_ref_pat_red],       "redundant patterns");
   ("pat_comp",    [warn_ref_pat_comp],                        "pattern compilation");
   ("resort",      [warn_ref_fun_resort; warn_ref_rec_resort], "resorted record fields and function clauses");
   ("no_dec_eq",   [warn_ref_no_decidable_eq],                 "equality of type is undecidable");
   ("gen",         [warn_ref_general],                         "miscellaneous warnings")];;


let warn_arg_fun (f : warn_level -> unit) = Arg.Symbol (["ign"; "warn"; "verb"; "err"], (function 
   "ign" -> f Level_Ignore
 | "warn" -> f Level_Warn
 | "verb" -> f Level_Warn_Verbose
 | "err" -> f Level_Error
 | _ -> f Level_Warn))

let warn_arg_fun_full refL = warn_arg_fun (fun l ->  List.iter (fun r -> r := l) refL)

(* Now process it to get the real thing that the Arg-Lib can handle *)
let warn_opts = 
  let prefix_doc refL d = " warning level of "^d in
  let process_option (p, refL, d) = 
    let real_arg = ("-wl_"^p) in
    let real_doc = prefix_doc refL d in
    let mod_fun = warn_arg_fun_full refL in
     (real_arg, mod_fun, real_doc)
  in
  let sopts = List.map process_option warn_opts_aux in
  let all = ("-wl", warn_arg_fun_full warn_refL, prefix_doc warn_refL "all warnings")
  in (all :: sopts)


let report_warning env w =
  let level = warn_level w in  
  match level with
      Level_Ignore       -> ()
    | Level_Warn         -> (match dest_warning env false w with None -> () | Some (b, l, m) -> print_err false false true  l "Warning" m)
    | Level_Warn_Verbose -> (match dest_warning env true  w with None -> () | Some (b, l, m) -> print_err false b     false l "Verbose warning" m)
    | Level_Error        -> (match dest_warning env true  w with None -> () | Some (b, l, m) -> print_err true  b     false l "Error"   m)

(******************************************************************************)
(* Debuging                                                                   *)
(******************************************************************************)

let debug_flag = ref true

let print_debug s =
  if (not !debug_flag) then () else
  (Format.eprintf "DEBUG: %s\n\n" s;
   Format.pp_print_flush Format.err_formatter ())

let print_debug_data f s xs =
  let xs_s = List.map (fun x -> Ulib.Text.to_string (f x)) xs in
  print_debug (s ^ "\n" ^ (String.concat "\n" xs_s))

let print_debug_exp env = 
  let module B = Backend.Make(struct
    let avoid = (false, (fun _ -> true), Name.fresh);;
    let env = env
  end) in
  print_debug_data B.ident_exp

let print_debug_pat env = 
  let module B = Backend.Make(struct
    let avoid = (false, (fun _ -> true), Name.fresh);;
    let env = env
  end) in
  print_debug_data B.ident_pat

let print_debug_def env = 
  let module B = Backend.Make(struct
    let avoid = (false, (fun _ -> true), Name.fresh);;
    let env = env
  end) in
  print_debug_data B.ident_def

let print_debug_typ env = 
  let module B = Backend.Make(struct
    let avoid = (false, (fun _ -> true), Name.fresh);;
    let env = env
  end) in
  print_debug_data B.ident_typ

let print_debug_src_t env = 
  let module B = Backend.Make(struct
    let avoid = (false, (fun _ -> true), Name.fresh);;
    let env = env
  end) in
  print_debug_data B.ident_src_t

