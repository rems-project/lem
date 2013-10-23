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

open Typed_ast
open Typed_ast_syntax
open Types
open Target
open Process_file

let (^^) = Filename.concat
let r = Ulib.Text.of_latin1


(** Build type_defs for build-in types *)
let tds = 
  [(Path.listpath, mk_tc_type [Ty(Tyvar.from_rope (r"a"))] None);
   (Path.setpath, mk_tc_type [Ty(Tyvar.from_rope (r"a"))] None);
   (Path.vectorpath, mk_tc_type [Ty(Tyvar.from_rope (r"b"));Nv(Nvar.from_rope (r"a"))] None);
   (Path.natpath, mk_tc_type [] None);
   (Path.stringpath, mk_tc_type [] None);
   (Path.boolpath, mk_tc_type [] None);
   (Path.bitpath, mk_tc_type [] None);
   (Path.charpath, mk_tc_type [] None);
   (Path.numeralpath, mk_tc_type [] None);
   (Path.unitpath, mk_tc_type [] None)]

let initial_d : Types.type_defs = 
  List.fold_right (fun x y -> Types.Pfmap.insert y x) tds Types.Pfmap.empty

let initial_local_env : Typed_ast.local_env =
  { empty_local_env with
    p_env = Nfmap.from_list 
              [(Name.from_rope (r"bool"), (Path.boolpath, Ast.Unknown));
               (Name.from_rope (r"bit"), (Path.bitpath, Ast.Unknown));
               (Name.from_rope (r"vector"), (Path.vectorpath, Ast.Unknown));
               (Name.from_rope (r"set"), (Path.setpath, Ast.Unknown));
               (Name.from_rope (r"list"), (Path.listpath, Ast.Unknown));
               (Name.from_rope (r"string"), (Path.stringpath, Ast.Unknown));
               (Name.from_rope (r"char"), (Path.charpath, Ast.Unknown));
               (Name.from_rope (r"numeral"), (Path.numeralpath, Ast.Unknown));
               (Name.from_rope (r"unit"), (Path.unitpath, Ast.Unknown));
               (Name.from_rope (r"nat"), (Path.natpath, Ast.Unknown))] }


let initial_env : Typed_ast.env =
  { empty_env with local_env = initial_local_env; t_env = initial_d }

let space = Str.regexp "[ \t\n]+"

let read_constants file =
  let i = open_in file in
  let rec f () =
    try 
      let s = input_line i in
        List.map Ulib.Text.of_latin1 (Str.split space s) @ f ()
    with
      | End_of_file ->
          close_in i;
          []
  in 
  let const_list = f() in
  let const_set = List.fold_left (fun s c -> NameSet.add (Name.from_rope c) s) NameSet.empty const_list in
  const_set

let read_target_constants lib_path targ =
  match targ with
    | Target_ident -> NameSet.empty
    | Target_no_ident targ' -> (try 
        read_constants (lib_path ^^ (non_ident_target_to_string targ' ^ "_constants"))
      with _ -> NameSet.empty)
