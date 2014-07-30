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

open Process_file
open Debug
open Module_dependencies
open Typed_ast

let backends = ref ([] : Target.target list)
let suppress_renaming = ref false

let add_backend b () : unit = if not (List.mem b !backends) then (backends := b::!backends)

let opt_print_env = ref false
let opt_print_version = ref false
let lib = ref []
let out_dir = ref None
let tex_all_filename_opt = ref None
let opt_file_arguments = ref ([]:string list)

let default_library = 
   try 
     let lp = Sys.getenv("LEMLIB") in
     if Filename.is_relative lp 
     then Filename.concat (Sys.getcwd ()) lp
     else lp
   with 
     | Not_found -> Filename.concat Build_directory.d "library"

let lib_paths_ref = ref ([] : string list)
let allow_reorder_modules = ref true

let options = Arg.align ([
  ( "-ocaml", 
    Arg.Unit (add_backend (Target.Target_no_ident Target.Target_ocaml)),
    " generate OCaml");
  ( "-tex", 
    Arg.Unit (add_backend (Target.Target_no_ident Target.Target_tex)),
    " generate LaTeX for each module separatly");
  ( "-tex_all", 
    Arg.String (fun fn -> tex_all_filename_opt := Some fn),
    " generate LaTeX in a single file");
  ( "-html", 
    Arg.Unit (add_backend (Target.Target_no_ident Target.Target_html)),
    " generate Html");
  ( "-hol", 
    Arg.Unit (add_backend (Target.Target_no_ident Target.Target_hol)),
    " generate HOL");
  ( "-isa",
    Arg.Unit (add_backend (Target.Target_no_ident Target.Target_isa)),
    " generate Isabelle");
  ( "-coq",
    Arg.Unit (add_backend (Target.Target_no_ident Target.Target_coq)),
    " generate Coq");
  ( "-lem",
    Arg.Unit (add_backend (Target.Target_no_ident Target.Target_lem)),
    " generate Lem output after simple transformations");
  ( "-ident",
    Arg.Unit (add_backend Target.Target_ident),
    " generate input on stdout\n\n");

  ( "-lib", 
    Arg.String (fun l -> lib_paths_ref := l :: (!lib_paths_ref)),
    " add path to library path; if no lib is given the default '"^(default_library)^")' is used. Set LEMLIB environment variable to change this default.");
  ( "-no_dep_reorder", 
    Arg.Clear allow_reorder_modules,
    " prohibit reordering modules given to lem as explicit arguments in order during dependency resolution\n\n");

  ( "-outdir", 
    Arg.String (fun l -> out_dir := Some l),
    " the output directory (the default is the dir the files reside in)");
  ( "-i", 
    Arg.String (fun l -> lib := l::!lib),
    " treat the file as input only and generate no output for it");
  ( "-only_changed_output",
    Arg.Clear Process_file.always_replace_files, 
    " generate only output files, whose content really changed compared to the existing file");
  ( "-only_auxiliary",
    Arg.Set Process_file.only_auxiliary, 
    " generate only auxiliary output files");
  ( "-auxiliary_level", 
    Arg.Symbol (["none"; "auto"; "all"], (fun s ->
     Backend.gen_extra_level := (match s with
       | "none" -> 0
       | "auto" -> 1
       | _ -> 2))),
    " generate no (none) auxiliary-information, only auxiliaries that can be handled automatically (auto) or all (all) auxiliary information\n\n");

  ( "-debug",
    Arg.Unit (fun () -> Printexc.record_backtrace true),
    " print a backtrace for all errors (lem needs to be compiled in debug mode)");
  ( "-print_env",
    Arg.Set opt_print_env, 
    " print the environment signature on stdout");
  ( "-add_loc_annots", 
    Arg.Set Backend_common.def_add_location_comment_flag, 
    " add location annotations to the output");
  ( "-add_full_isa_lib_path",
    Arg.Set Backend_common.isa_add_full_library_path_flag, 
    " add the full path of the isabelle-lib directory to Isabelle import statements");
  ( "-v",
    Arg.Set opt_print_version, 
    " print version");
  ( "-ident_pat_compile",
    Arg.Unit (fun () -> Target_trans.ident_force_pattern_compile := true; Reporting.ignore_pat_compile_warnings()),
    " activates pattern compilation for the identity backend. This is used for debugging.");
  ( "-ident_dict_passing",
    Arg.Set Target_trans.ident_force_dictionary_passing, 
    " activates dictionary passing transformations for the identity backend. This is used for debugging.");
  ( "-tex_suppress_target_names",
  	Arg.Set Backend.suppress_target_names,
  	" prints target-specific let-bindings as normal let bindings in the TeX backend.");
  ( "-tex_include_libraries",
  	Arg.Clear Backend.suppress_libraries,
  	" include libraries in the TeX backend.");
  ( "-hol_remove_matches",
    Arg.Set Target_trans.hol_remove_matches, 
    " try to remove toplevel matches in HOL4 output."); (* This is generally useful, but disabled by default for compatibility with old Lem versions. *)
  ( "-prover_remove_failwith",
    Arg.Set Target_trans.prover_remove_failwith, 
    " remove failwith branches in match statements in the prover backends.");
  ( "-suppress_renaming",
  	Arg.Set suppress_renaming,
  	" suppresses Lem's renaming facilities.");
  ( "-report_default_instance_invocation",
    Arg.Set Types.report_default_instance_invocation,
    " reports the name of any default instance invoked at a given type.")
] @ Reporting.warn_opts)

let usage_msg = 
    ("Lem " ^ Version.v ^ "\n"
     ^ "example usage:       lem -hol -ocaml test.lem\n" 
    )

let _ = 
  Arg.parse options 
    (fun s -> 
      opt_file_arguments := (!opt_file_arguments) @ [s])
    usage_msg


let check_modules env modules =
  (* The checks. Modify these lists to add more. *)
  let exp_checks env = [Patterns.check_match_exp_warn env; Syntactic_tests.check_id_restrict_e env] in
  let pat_checks env = [Syntactic_tests.check_id_restrict_p env; Patterns.check_number_patterns env] in
  let def_checks env = [Patterns.check_match_def_warn env;
                        Syntactic_tests.check_decidable_equality_def env;
		        Syntactic_tests.check_positivity_condition_def] in

  (* Use the Macro_expander to execute these checks *)
  let module Ctxt = struct let avoid = None let env_opt = Some(env) end in
  let module M = Macro_expander.Expander(Ctxt) in
  let exp_mac env = Macro_expander.list_to_mac (List.map (fun f _ e -> (let _ = f e in None)) (exp_checks env)) in
  let exp_ty env ty = ty in
  let exp_src_ty env src_t = src_t in
  let exp_pat env = Macro_expander.list_to_bool_mac (List.map (fun f _ _ p -> (let _ = f p in None)) (pat_checks env)) in
  let check_defs env defs = begin
    let _ = M.expand_defs (List.rev defs) (exp_mac env, exp_ty env, exp_src_ty env, exp_pat env) in
    let _ = List.map (fun d -> List.map (fun c -> c d) (def_checks env)) defs in
    ()
  end in
  let check_module m = (if m.Typed_ast.generate_output then 
    (let (defs, _) = m.Typed_ast.typed_ast in check_defs env defs)) in
  let _ = List.map check_module modules in
  ()

let print_compile_messages env targ modules = begin
  let modules' = List.filter (fun m -> m.Typed_ast.generate_output) modules in
  let used_entities = Typed_ast_syntax.get_checked_modules_entities targ false modules' in

  let print_const_ref c = begin
    let cd = Typed_ast.c_env_lookup Ast.Unknown env.Typed_ast.c_env c in
    match Target.Targetmap.apply_target cd.Typed_ast.compile_message targ with
      | None -> ()
      | Some m -> Reporting.report_warning env (Reporting.Warn_compile_message 
          (cd.Typed_ast.spec_l, targ, cd.Typed_ast.const_binding, m))
  end in
  List.iter print_const_ref used_entities.Typed_ast_syntax.used_consts
end

(* check that the environment is OK for the target. Perhaps throw warnings or raise exceptions. *)
let check_env_for_target targ env : unit =
begin
  let _ = Typed_ast_syntax.check_for_inline_cycles targ env.Typed_ast.c_env in
  ()
end

let transform_for_target libpath modules env targ =
  let consts = Initial_env.read_target_constants libpath targ in

  let _ = check_env_for_target targ env in

  let trans = Target_trans.get_transformation targ in
  try
    let (env',transformed_m) = 
      List.fold_left 
        (fun (env,new_mods) old_mod -> 
           let _ = Reporting.warnings_active := old_mod.Typed_ast.generate_output in
           let (env,m) = trans env old_mod in
             (env,m::new_mods))
        (env,[])
        modules
    in     
    let transformed_m = List.rev transformed_m in 

    let _ = Reporting.warnings_active := true in
    let _ = print_compile_messages env targ modules in

    (* perform renamings *)
    if not (!suppress_renaming) then
	    let used_entities = Typed_ast_syntax.get_checked_modules_entities targ false transformed_m in
  	  let env'' = Rename_top_level.rename_defs_target targ used_entities consts env' in

  	  let consts' = Target_trans.add_used_entities_to_avoid_names env'' targ used_entities consts in
  	  let transformed_m' = Target_trans.rename_def_params targ consts' transformed_m in

  	  let avoid = Target_trans.get_avoid_f targ consts' in
  	  (env'', avoid, transformed_m')
  	else
  	 	let f utxt name_f = Name.from_rope utxt in
  	 	let empty_var_avoid_f = (false, (fun x -> true), f) in
	  	 	(env', empty_var_avoid_f, transformed_m)
  with
      | Trans.Trans_error(l,msg) ->
          raise (Reporting_basic.Fatal_error (Reporting_basic.Err_trans (l, msg)))

let per_target libpath tex_all_opt (out_dir : string option) modules env targ =
  let (env', avoid, transformed_mods) = transform_for_target libpath modules env targ in
  (if (targ = Target.Target_no_ident Target.Target_tex) then begin
     match tex_all_opt with
       | None -> output env' avoid targ out_dir transformed_mods
       | Some (dir, filename, gen_single) ->
            if gen_single then output env' avoid targ out_dir transformed_mods;
            output_alltexdoc env' avoid dir filename transformed_mods
   end else
     output env' avoid targ out_dir transformed_mods);
  env'


let main () =
  let _ = if !opt_print_version then print_string ("Lem " ^ Version.v ^ "\n") in
  let lib_path = begin
    let l = List.rev !lib_paths_ref in
    let l' = default_library :: l in
    List.map (fun lp ->
          if Filename.is_relative lp then
            Filename.concat (Sys.getcwd ()) lp
          else
            lp) l'
  end in
  let _ = 
    List.iter
      (fun f -> if not (Filename.check_suffix f ".lem")
      then raise (Failure "Files must have .lem extension"))
      (!opt_file_arguments @ !lib)
  in
  let _ = 
    List.iter
      (fun f ->
         if not (Str.string_match (Str.regexp "[A-Za-z]") (Filename.basename f) 0) then
           raise (Failure(".lem filenames must start with a letter")))
      (!opt_file_arguments @ !lib)
  in
  (* do not do caching just now, perhaps activate later again, but if we do, then in
     Initial_env
  let init =
    try
      let inchannel = open_in (Filename.concat lib_path "lib_cache") in
      let v = input_value inchannel in
        close_in inchannel;
        v
    with
      | Sys_error _ ->
          let module I = Initial_env.Initial_libs(struct let path = lib_path end) in
          let outchannel = open_out (Filename.concat lib_path "lib_cache") in
            output_value outchannel I.init;
            close_out outchannel;
            I.init
  in*)


  (* check whether all the files are in one directory *)
  let out_dir_compute = match !opt_file_arguments with
    | [] -> Some (Filename.current_dir_name)
    | f :: fs -> begin
        let d = Filename.dirname f in
        if (List.exists (fun f -> not (Filename.dirname f = d)) fs) 
          then None else Some d
      end
  in
  let out_dir = match (!out_dir, out_dir_compute) with
    | (Some _, None) -> raise (Reporting_basic.Fatal_error (Reporting_basic.Err_general (false, Ast.Unknown, "in order to use '-outdir' all files given as arguments to Lem need to be in the same directory")));
    | (x, _) -> x
  in

  let tex_all_opt = begin
     match (!tex_all_filename_opt) with
       | None -> None
       | Some fn -> begin
           let dir0 = Filename.dirname fn in
           let dir = if dir0 = "" then Filename.current_dir_name else dir0 in
           let filename0 = Filename.basename fn in
           let filename = if (Filename.check_suffix filename0 ".tex") then Filename.chop_extension filename0 else filename0 in
           let generate_single_tex = List.mem (Target.Target_no_ident Target.Target_tex) !backends in
           let _ = add_backend (Target.Target_no_ident Target.Target_tex) () in
           Some (dir, filename, generate_single_tex)
       end
  end in

  (* We don't want to add the files in !lib to the resulting module ASTs,
     because we don't want to put them throught the back end. So, they get an argument false, while all others get true. *)
  let files_to_process =
      (List.map (fun x -> (x, false)) (List.rev !lib) @ 
       List.map (fun x -> (x, true)) !opt_file_arguments)
  in

  (* Parse all of the .lem sources and also parse depencies *)
  let processed_files = Module_dependencies.process_files (!allow_reorder_modules) lib_path files_to_process in
  
  let backend_set = 
    List.fold_right 
      (fun x s ->
         match Target.dest_human_target x with
           | None -> s
           | Some(t) -> Target.Targetset.add t s)
       !backends
    Target.Targetset.empty 
  in

  (* Typecheck all of the .lem sources *)
  let (modules, env) =
    List.fold_left
      (fun (mods, env) (mod_name, file_name, ast, add_to_modules) ->
         let mod_name_name = Name.from_string mod_name in

         let im : Path.t list = begin 
           let im_direct = Ast_util.get_imported_modules ast in
           let get_rec_deps (p, _) = begin p :: (match Util.option_first (fun mr -> if (Path.compare mr.module_path p = 0) then Some mr.imported_modules_rec else None) mods with
             | None -> []
             | Some imr -> Util.rev_flatten (List.rev_map (function IM_targets _ -> [] | IM_paths ps -> ps) imr))
           end in
           Util.rev_flatten (List.rev_map get_rec_deps im_direct)
         end in

         let m_env' = Nfmap.filter (fun mod_name mod_path -> List.exists (fun p -> Path.compare mod_path p = 0) im) env.local_env.m_env in
         let env' = {env with local_env = {env.local_env with m_env = m_env'}} in
         let (e,tast) = Typecheck.check_defs backend_set mod_name_name file_name add_to_modules env' ast in
         let e = {e with local_env = {e.local_env with m_env = Nfmap.union env.local_env.m_env e.local_env.m_env}} in

         let imported_mods = Backend_common.get_imported_target_modules tast in
         let get_rec_imported_mods = function 
           | IM_targets _ -> []
           | IM_paths ps -> Util.rev_flatten (List.rev_map (fun p -> begin
               Util.option_default [] (Util.option_first (fun mr -> if (Path.compare mr.module_path p = 0) then Some mr.imported_modules_rec else None) mods)
             end) ps)
         in
         let module_record = 
           { Typed_ast.filename = file_name;
             Typed_ast.module_path = Path.mk_path [] mod_name_name;
             Typed_ast.imported_modules = imported_mods;
             Typed_ast.imported_modules_rec = List.fold_left (fun acc z -> List.rev_append (get_rec_imported_mods z) acc) (List.rev imported_mods) imported_mods;
             Typed_ast.untyped_ast = ast;
             Typed_ast.typed_ast = tast;
             Typed_ast.generate_output = add_to_modules }
         in
            (module_record::mods, e))
      ([],Initial_env.initial_env)
      (* We don't want to add the files in !lib to the resulting module ASTs,
       * because we don't want to put them throught the back end *)
      processed_files
  in

  (* Check the parsed source and produce warnings for various things. Currently:
     - non-exhaustive and redundant patterns
  *)
  let _ = check_modules env modules in

  let _ = if !opt_print_env then
             begin
               Process_file.output_sig Format.std_formatter env
             end in


  let _ = List.fold_left (fun env -> (per_target default_library tex_all_opt out_dir (List.rev modules) env))
    env !backends in
  ()


let _ = 
  try 
    begin
      try ignore(main ()) 
      with  Failure(s) -> raise (Reporting_basic.err_general false Ast.Unknown ("Failure "^s))
    end
  with Reporting_basic.Fatal_error e -> Reporting_basic.report_error e

