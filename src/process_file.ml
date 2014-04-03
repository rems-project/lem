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

open Format
open Typed_ast

(* XXX: for debugging the developing code: open Coq_ast *)

let r = Ulib.Text.of_latin1

let get_lexbuf fn =
  let lexbuf = Lexing.from_channel (open_in fn) in
    lexbuf.Lexing.lex_curr_p <- { Lexing.pos_fname = fn;
                                  Lexing.pos_lnum = 1;
                                  Lexing.pos_bol = 0;
                                  Lexing.pos_cnum = 0; };
    lexbuf

let parse_file (f : string) : (Ast.defs * Ast.lex_skips) =
  let lexbuf = get_lexbuf f in
    try
      Parser.file (Lexer.token []) lexbuf
    with
      | Parsing.Parse_error ->
          let pos = Lexing.lexeme_start_p lexbuf in
          raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax (pos, "")))
      | Ast.Parse_error_locn(l,m) ->
          raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax_locn (l, m)))
      | Lexer.LexError(c,p) ->
          raise (Reporting_basic.Fatal_error (Reporting_basic.Err_lex (p, c)))

type instances = Types.instance list Types.Pfmap.t

let open_output_with_check dir file_name =
  let (temp_file_name, o) = Filename.open_temp_file "lem_temp" "" in
  (o, (o, temp_file_name, Filename.concat dir file_name)) 

let always_replace_files = ref true 
let only_auxiliary = ref false

let close_output_with_check (o, temp_file_name, file_name) =
  let _ = close_out o in
  let do_replace = !always_replace_files || (not (Util.same_content_files temp_file_name file_name)) in 
  let _ = if (not do_replace) then Sys.remove temp_file_name 
          else Util.move_file temp_file_name file_name in                   
  ()

let generated_line f = 
  Printf.sprintf "Generated by Lem from %s." f

let tex_preamble single_module = 
  "\\documentclass{article}\n" ^
  "\\usepackage{amsmath,amssymb}\n" ^
  "\\usepackage{color}\n" ^
  "\\usepackage{geometry}\n" ^
  "\\usepackage{alltt}\n" ^
  "\\usepackage{lem}\n" ^
  "\\geometry{a4paper,dvips,twoside,left=22.5mm,right=22.5mm,top=20mm,bottom=30mm}\n" ^
  "\\setlength{\\parindent}{0pt}\n" ^
  "\\begin{document}\n"^
  (if single_module then "" else "\\tableofcontents\n")
  
let tex_postamble = 
  "\\end{document}\n"

let html_preamble title = 
"\n" ^
"<?xml version=\"1.0\" encoding=\"utf-8\"?>\n" ^
"<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.1//EN\"\n" ^
"          \"http://www.w3.org/TR/xhtml11/DTD/xhtml11.dtd\">\n" ^
"<html xmlns=\"http://www.w3.org/1999/xhtml\">\n" ^
"  <head>\n" ^
"    <meta http-equiv=\"Content-Type\" content=\"text/html; charset=UTF-8\"/> \n" ^
"    <title>" ^ title ^ "</title>\n" ^
"    <link rel=\"stylesheet\" type=\"text/css\" title=\"lem style\" media=\"screen\" href=\"lem.css\"/>\n" ^
"  </head>\n" ^
"  <body>\n" ^
"    <h1 id=\"title\">" ^ title ^ "</h1>\n" ^
"<pre>\n"

let html_postamble = 
"\n" ^
"</pre>\n" ^
"  </body>\n" ^
"</html>\n"


let output_tex_files single_module gen_string r_main r_inc r_usage dir filename =
   (* main Tex-file *)
   let (o, ext_o) = open_output_with_check dir (filename ^ ".tex") in
     Printf.fprintf o "%s" gen_string;
     Printf.fprintf o "%s" (tex_preamble single_module);
     Printf.fprintf o "%s" (Ulib.Text.to_string r_main);
     Printf.fprintf o "%s" tex_postamble;
   close_output_with_check ext_o;

    (* tex definitions to include in other documents *)
   let (o,ext_o) = open_output_with_check dir (filename ^ "-inc.tex") in
     Printf.fprintf o "%s" gen_string;
     Printf.fprintf o "%s" (Ulib.Text.to_string r_inc);
   close_output_with_check ext_o;
   let (o, ext_o) = open_output_with_check dir (filename ^ "-use_inc.tex") in
     Printf.fprintf o "%s" gen_string;
     Printf.fprintf o "%s" (tex_preamble single_module);
     Printf.fprintf o "\\include{%s}\n" (filename ^ "-inc");
     Printf.fprintf o "%s" (Ulib.Text.to_string r_usage);
     Printf.fprintf o "%s" tex_postamble;
   close_output_with_check ext_o


let output1 env (out_dir : string option) (targ : Target.target) avoid m =
  let dir = Util.option_default (Filename.dirname m.filename) out_dir in
  let module C = struct
    let avoid = avoid
    let env = env
    let dir = dir
  end
  in
  let module B = Backend.Make(C) in
  let open Typed_ast in
  
  let imported_modules = Backend_common.imported_modules_to_strings env targ dir m.imported_modules in
  let extra_imported_modules = Util.remove_duplicates (imported_modules @ [Backend_common.get_module_open_string env targ dir m.module_path]) in
  let (mod_path, mod_name) = Path.to_name_list m.module_path in
  let module_name = Name.to_string (Backend_common.get_module_name env targ mod_path mod_name) in
    match targ with
      | Target.Target_ident ->
          let r = B.ident_defs m.typed_ast in
            Printf.printf "%s" (Ulib.Text.to_string r)
      | Target.Target_no_ident (Target.Target_lem) -> 
          begin
            let r = B.lem_defs m.typed_ast in
            let module_name_lower = String.uncapitalize module_name in
            let (o, ext_o) = open_output_with_check dir (module_name_lower ^ "-processed.lem") in
              Printf.fprintf o "%s" (Ulib.Text.to_string r);
              close_output_with_check ext_o
          end
      | Target.Target_no_ident (Target.Target_html) -> 
          begin
            let r = B.html_defs m.typed_ast in
            let (o, ext_o) = open_output_with_check dir (module_name ^ ".html") in
              Printf.fprintf o "<!-- %s -->\n" (generated_line m.filename);
              Printf.fprintf o "%s" (html_preamble module_name);
              Printf.fprintf o "%s" (Ulib.Text.to_string r);
              Printf.fprintf o "%s" html_postamble;
              close_output_with_check ext_o
          end
      | Target.Target_no_ident (Target.Target_hol) ->
          begin
            let (r_main, r_extra_opt) = B.hol_defs m.typed_ast in
            let hol_header load_mods o = begin
              Printf.fprintf o "(*%s*)\n" (generated_line m.filename);
              Printf.fprintf o "open HolKernel Parse boolLib bossLib;\n";
              if (List.length load_mods > 0) then begin
                Printf.fprintf o "open %s;\n\n" (String.concat " " load_mods)
              end;
              Printf.fprintf o "val _ = numLib.prefer_num();\n\n";
              Printf.fprintf o "\n\n";
            end in
            let _ = if (!only_auxiliary) then () else begin
              let (o, ext_o) = open_output_with_check dir (module_name ^ "Script.sml") in
              hol_header imported_modules o;
              Printf.fprintf o "val _ = new_theory \"%s\"\n\n" module_name;
       
              Printf.fprintf o "%s" (Ulib.Text.to_string r_main);
              Printf.fprintf o "val _ = export_theory()\n\n";
              close_output_with_check ext_o;
            end in
            let _ = match r_extra_opt with None -> () | Some r_extra ->
              begin
                let (o,ext_o) = open_output_with_check dir (module_name ^ "AuxiliaryScript.sml") in
                hol_header extra_imported_modules o;
                Printf.fprintf o "open lemLib;\n";
                Printf.fprintf o "(* val _ = lemLib.run_interactive := true; *)\n";
                Printf.fprintf o "val _ = new_theory \"%sAuxiliary\"\n\n" module_name;
                Printf.fprintf o "%s" (Ulib.Text.to_string r_extra);
                Printf.fprintf o "val _ = export_theory()\n\n";
                close_output_with_check ext_o
              end in ()
          end
      | Target.Target_no_ident (Target.Target_tex) -> 
          begin
            let r_main = B.tex_defs m.typed_ast in
            let (r_inc,r_usage) = B.tex_inc_defs m.typed_ast in
            let gen_string = Printf.sprintf "%%%s\n" (generated_line m.filename) in
            let _ = output_tex_files true gen_string r_main r_inc r_usage dir module_name in
            ()
          end
      | Target.Target_no_ident(Target.Target_ocaml) -> 
          begin
            let (r_main, r_extra_opt) = B.ocaml_defs m.typed_ast in
            let module_name_lower = String.uncapitalize module_name in
            let _ = if (!only_auxiliary) then () else begin
              let (o, ext_o) = open_output_with_check dir (module_name_lower ^ ".ml") in
              Printf.fprintf o "(*%s*)\n" (generated_line m.filename);
              Printf.fprintf o "%s" (Ulib.Text.to_string r_main);
              close_output_with_check ext_o
            end in
            let _ = match r_extra_opt with None -> () | Some r_extra ->
              begin
                let (o, ext_o) = open_output_with_check dir (module_name_lower ^ "Auxiliary.ml") in
                Printf.fprintf o "(*%s*)\n" (generated_line m.filename);
                List.iter (fun s -> Printf.fprintf o "open %s\n\n" s) extra_imported_modules;
  
                Printf.fprintf o "%s" "let run_test n loc b =\n  if b then (Format.printf \"%s: ok\\n\" n) else ((Format.printf \"%s: FAILED\\n  %s\\n\\n\" n loc); exit 1);;\n\n";

                Printf.fprintf o "%s" (Ulib.Text.to_string r_extra);
                close_output_with_check ext_o
             end in ()
          end
      | Target.Target_no_ident(Target.Target_isa) -> 
          begin
          try begin
            let (r_main, r_extra_opt) = B.isa_defs m.typed_ast in
            let _ = if (!only_auxiliary) then () else 
              begin
                let (o, ext_o) = open_output_with_check dir (module_name ^ ".thy") in 
                let r1 = B.isa_header_defs m.typed_ast in
                Printf.fprintf o "header{*%s*}\n\n" (generated_line m.filename);
                Printf.fprintf o "theory \"%s\" \n\n" module_name;
                Printf.fprintf o "imports \n \t Main\n";
(*                Printf.fprintf o "\t \"%s\"\n" isa_thy; *)
                (*
                Printf.fprintf o "imports \n \t \"%s/num_type\" \n" libpath;
                 *)
                Printf.fprintf o "%s" (Ulib.Text.to_string r1);
                begin 
                  if imported_modules <> [] then 
                    begin
                      List.iter (fun f -> Printf.fprintf o "\t \"%s\" \n" f) imported_modules
                    end;
                end;

                Printf.fprintf o "\nbegin \n\n";
                Printf.fprintf o "%s" (Ulib.Text.to_string r_main);
                Printf.fprintf o "end\n";
                close_output_with_check ext_o
              end in

              let _ = match r_extra_opt with None -> () | Some r_extra ->
              begin
                let (o, ext_o) = open_output_with_check dir (module_name ^ "Auxiliary.thy") in              
                Printf.fprintf o "header{*%s*}\n\n" (generated_line m.filename);
                Printf.fprintf o "theory \"%sAuxiliary\" \n\n" module_name;
                Printf.fprintf o "imports \n \t Main \"~~/src/HOL/Library/Code_Target_Numeral\"\n";
(*                Printf.fprintf o "\t \"%s\"\n" isa_thy; *)
                begin 
                  if extra_imported_modules <> [] then 
                    begin
                      List.iter (fun f -> Printf.fprintf o "\t \"%s\" \n" f) extra_imported_modules
                    end;
                end;
                Printf.fprintf o "\nbegin \n\n";
                Printf.fprintf o "%s" (Ulib.Text.to_string r_extra);
                Printf.fprintf o "end\n";
                close_output_with_check ext_o
              end in ()
            end
            with | Trans.Trans_error(l,msg) ->
                    raise (Reporting_basic.Fatal_error (Reporting_basic.Err_trans_header (l, msg)))
          end

      | Target.Target_no_ident(Target.Target_coq) -> 
          try begin
            let (r, r_extra) = B.coq_defs m.typed_ast in
            let _ = if (!only_auxiliary) then () else 
              begin
                let (o, ext_o) = open_output_with_check dir (module_name ^ ".v") in
                  Printf.fprintf o "(* %s *)\n\n" (generated_line m.filename);
                  Printf.fprintf o "Require Import Arith.\n";
                  Printf.fprintf o "Require Import Bool.\n";
                  Printf.fprintf o "Require Import List.\n";
                  Printf.fprintf o "Require Import String.\n";
                  Printf.fprintf o "Require Import Program.Wf.\n\n";
                  Printf.fprintf o "Require Import coqharness.\n\n";
                  Printf.fprintf o "Open Scope nat_scope.\n";
                  Printf.fprintf o "Open Scope string_scope.\n\n";
                  Printf.fprintf o "%s" (Ulib.Text.to_string r);
                  close_output_with_check ext_o
              end
            in

            let _ =
              begin
                let (o, ext_o) = open_output_with_check dir (module_name ^ "_auxiliary.v") in
                  Printf.fprintf o "(* %s *)\n\n" (generated_line m.filename);
                  Printf.fprintf o "Require Import Arith.\n";
                  Printf.fprintf o "Require Import Bool.\n";
                  Printf.fprintf o "Require Import List.\n";
                  Printf.fprintf o "Require Import String.\n";
                  Printf.fprintf o "Require Import Program.Wf.\n\n";
                  Printf.fprintf o "Open Scope nat_scope.\n";
                  Printf.fprintf o "Open Scope string_scope.\n\n";
                  Printf.fprintf o "%s" (Ulib.Text.to_string r_extra);
                  close_output_with_check ext_o
              end in ()
          end
            with
              | Trans.Trans_error(l,msg) ->
                  raise (Reporting_basic.Fatal_error (Reporting_basic.Err_trans_header (l, msg)))

let output env consts (targ : Target.target)  (out_dir : string option) mods =
  List.iter
    (fun m ->
       if m.generate_output then
       output1 env out_dir targ consts m)
    mods


let output_alltexdoc env avoid dir f mods = 
  let module C = struct
    let avoid = avoid
    let env = env
    let dir = dir
  end
  in
  let module B = Backend.Make(C) in
  let (^^^^) = Ulib.Text.(^^^) in

  let (r_main, r_inc, r_usage) = List.fold_left (fun (r_main, r_inc, r_usage) m -> begin
     let r_main' = B.tex_defs m.typed_ast in
     let (r_inc',r_usage') = B.tex_inc_defs m.typed_ast in

     let (mod_path, mod_name) = Path.to_name_list m.module_path in
     let module_name = Name.to_string (Backend_common.get_module_name env (Target.Target_no_ident (Target.Target_tex)) mod_path mod_name) in
     let sect_header = r"\\clearpage\n\n\\section{" ^^^^ Output.tex_escape (Ulib.Text.of_string module_name) ^^^^ r"}\n" in
     (r_main ^^^^ sect_header ^^^^ r_main', 
      r_inc ^^^^ r_inc',
      r_usage ^^^^ sect_header ^^^^ r_usage')
    end) (r"", r"", r"") mods in

  let fs = String.concat " " (List.map (fun m -> m.filename) mods) in
  let gen_string = Printf.sprintf "%%%s\n" (generated_line fs) in
  let _ = output_tex_files false gen_string r_main r_inc r_usage dir f in
  ()







let ident_step i = i ^ "  "

let output_sig_const_descr o env ident n cd =
begin
  pp_print_string o (ident ^ "val " ^ Name.to_string n ^ " : ");
  Types.pp_typschm o cd.const_tparams cd.const_class cd.const_type;
  pp_print_newline o (); 
end

let output_sig_type o env indent n p = begin
  (match Types.Pfmap.apply env.t_env p with
    | Some(Types.Tc_class _) ->   pp_print_string o (indent ^ "class " ^ Name.to_string n);
    | Some(Types.Tc_type td) -> begin
        pp_print_string o (indent ^ "type " ^ Name.to_string n);
        List.iter (fun tv -> pp_print_string o " "; Types.pp_tnvar o tv) td.Types.type_tparams;
        begin match td.Types.type_abbrev with
          | None -> ();
          | Some t -> begin
               pp_print_string o " = ";
               Types.pp_type o t;
            end
        end;
        begin match td.Types.type_fields with
          | None -> ();
          | Some field_list -> 
               let indent' = "    " ^ indent in 
               let format_field f = begin
                 let fd = c_env_lookup Ast.Unknown env.c_env f in begin
                   output_sig_const_descr o env indent' (Path.get_name fd.const_binding) fd;
                   pp_print_newline o ();
                 end
               end in begin
               pp_print_string o " = {";
               pp_print_newline o ();
               List.iter format_field field_list;
               pp_print_string o (indent ^ "}");
            end
        end;
      end
    | _ -> ());
  pp_print_newline o (); 
end

let rec output_sig_local_env o env ident lenv =
begin  
  Nfmap.iter (fun n (p, _) -> 
    output_sig_type o env ident n p) lenv.p_env;
  pp_print_newline o ();

  Nfmap.iter (fun n r -> 
    let cd = c_env_lookup Ast.Unknown env.c_env r in
    output_sig_const_descr o env ident n cd) lenv.v_env;
  pp_print_newline o ();

  (* print submodules *)
  Nfmap.iter (fun n r -> 
    let md = e_env_lookup Ast.Unknown env.e_env r in
    output_sig_module o env ident md)  lenv.m_env;
end 

and output_sig_module o env ident md =
begin
  let (_, mod_name) = Path.to_name_list md.mod_binding in

  pp_print_string o (ident ^ "module " ^ Name.to_string mod_name ^ " = struct");
  pp_print_newline o ();
  output_sig_local_env o env (ident_step ident) md.mod_env;
  pp_print_string o (ident ^ "end");
  pp_print_newline o ();
  pp_print_newline o ();
end


let output_sig o env  =
  output_sig_local_env o env "" env.local_env;
