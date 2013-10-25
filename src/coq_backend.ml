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

open Backend_common
open Coq_backend_utils
open Output
open Typed_ast
open Typed_ast_syntax
open Target
open Types

let print_and_fail l s =
  raise (Reporting_basic.err_general true l s)
;;

let lex_skip =
	function
    | Ast.Com r -> ml_comment_to_rope r
    | Ast.Ws r -> r
    | Ast.Nl -> r"\n"
;;

let delim_regexp = Str.regexp "^\\([][`;,(){}]\\|;;\\)$"
;;

let symbolic_regexp = Str.regexp "^[-!$%&*+./:<=>?@^|~]+$"
;;

let is_delim s = Str.string_match delim_regexp s 0
;;

let is_symbolic s = Str.string_match symbolic_regexp s 0
;;

let is_abbreviation l =
	let length = Seplist.length l in
	let abbreviation =
		match Seplist.hd l with
    	| (_, _, _, Te_abbrev _, _) -> true
    	| _ -> false
  in
  	length = 1 && abbreviation
;;

let is_record l =
	let length = Seplist.length l in
	let record =
		match Seplist.hd l with
    	| (_, _, _, Te_record _, _) -> true
    	| _ -> false
  in
  	length = 1 && record
;;

let need_space x y =
	let f x =
  	match x with
    	| Kwd'(s) ->
      	if is_delim s then
        	(true,false)
        else if is_symbolic s then
          (false,true)
        else
          (false,false)
      | Ident'(r) ->
        (false, is_symbolic @@ Ulib.Text.to_string r)
      | Num' _ ->
        (false,false)
    in
    	let (d1,s1) = f x in
    	let (d2,s2) = f y in
      	not d1 && not d2 && s1 = s2
;;

let in_target targets = Typed_ast.in_targets_opt (Target.Target_no_ident Target.Target_coq) targets;;

let coq_infix_op a x =
  Output.flat [
    from_string "(fun x y => x "; id a x; from_string " y)"
  ]
;;

let coq_format_op use_infix =
  if use_infix then
    coq_infix_op
  else
    id

let none = Ident.mk_ident_strings [] "None";;
let some = Ident.mk_ident_strings [] "Some";;

let fresh_name_counter = ref 0
;;

module OutputSet = Set.Make (struct type t = Output.t let compare = Pervasives.compare end)
;;

let decidable_equality_tracker =
  let s = List.fold_right OutputSet.add [
      from_string "ascii_beq";
      from_string "string_beq";
      from_string "num_beq";
      from_string "bool_beq"
    ] OutputSet.empty
  in
    ref s
;;

let generate_fresh_name = fun () ->
  let old  = !fresh_name_counter in
  let _    = fresh_name_counter := old + 1 in
  let post = string_of_int old in
    Pervasives.(^) "x" post
;;

let rec generate_coq_decidable_equality' t =
  match t with
     | Typ_wild _ -> None
     | Typ_var (_, _) -> None
     | Typ_len _ -> None
     | Typ_fn (src, _, dom) -> None
     | Typ_tup srct_skiplist -> assert false
     | Typ_app (id, typ) -> assert false
     | Typ_backend (id, typ) -> assert false
     | Typ_paren (_, src, _) -> generate_coq_decidable_equality' src.term
;;

let error o =
  from_string "(* unable to generate decidable equality for " ^ o ^ from_string " *)"
;;

let lskips_t_to_string name =
  let (lskips_t, _) = name in
    kwd (Ulib.Text.to_string @@ Name.to_rope (Name.strip_lskip lskips_t))
;;

module CoqBackendAux (A : sig val avoid : var_avoid_f option;; val env : env;; val ascii_rep_set : Types.Cdset.t end) =
  struct

    module B = Backend_common.Make (
      struct
        let env = A.env
        let target = Target_no_ident Target_coq
        let id_format_args = (coq_format_op, path_sep)
      end);;

    module C = Exps_in_context (
      struct
        let env_opt = Some A.env
        let avoid = A.avoid
      end)
    ;;

let use_ascii_rep_for_const (cd : const_descr_ref) : bool =
  Types.Cdset.mem cd A.ascii_rep_set
;;

let rec src_t_to_string =
  function
    | Typ_app (p, ts) ->
      let (name_list, name) = Ident.to_name_list (B.type_id_to_ident p) in
        from_string @@ Ulib.Text.to_string (Name.to_rope name)
    | Typ_backend (p, ts) ->
      let (name_list, name) = Path.to_name_list p.descr in
        from_string @@ Ulib.Text.to_string (Name.to_rope name)
    | Typ_var (_, v) ->
        id Type_var @@ Ulib.Text.(^^^) (r"") (Tyvar.to_rope v)
    | Typ_wild skips -> from_string "_"
    | Typ_len src_nexp -> from_string "(* src_t_to_string len *)"
    | Typ_fn (src_t, skips, src_t') -> from_string "(* src_t_to_string fn *)"
    | Typ_tup src_t_lskips_seplist -> from_string "(* src_t_to_string tuple *)"
    | Typ_paren (skips, src_t, skips') ->
        from_string "(" ^ src_t_to_string src_t.term ^ from_string ")"
;;
let typ_ident_to_output (p : Path.t id) =     
  Ident.to_output Type_ctor path_sep (B.type_id_to_ident p)

let field_ident_to_output fd ascii_alternative = 
  Ident.to_output Term_field path_sep (B.const_id_to_ident fd ascii_alternative)
;;

let const_name_to_output a n =
  Name.to_output Term_var n

let generate_coq_record_update_notation e =
  let notation_kwd = from_string "Notation" in
  let with_kwd = from_string "\'with\'" in
  let prefix =
    Output.flat [
      notation_kwd; from_string " \"{[ r "; with_kwd; from_string " "
    ]
  in
  let aux all_fields x =
    let ((n0, l), c, s4, ty) = x in
    let n = B.const_ref_to_name n0 false c in
    let name = Name.to_string (Name.strip_lskip n) in
    let all_fields = List.filter (fun x -> Pervasives.compare name x <> 0) all_fields in
    let other_fields = concat (kwd "; ")
      (List.map (fun x ->
        Output.flat [
          from_string x; from_string " := " ^ from_string x ^ from_string " r"
        ]
      ) all_fields)
    in
    let focussed_field = from_string name ^ from_string " := e" in
    let body =
      Output.flat [
        from_string "\'"; from_string name; from_string "\' := e ]}\" := "
      ]
    in
    let result =
      Output.flat [
        prefix; body; from_string "("; from_string "{| "; focussed_field;
        from_string "; "; other_fields; from_string " |})."
      ]
    in
      match all_fields with
        | []    -> emp (* DPM: this should have been macro'd away earlier *)
        | x::xs -> result
  in
    match e with
      | Te_record (s1, s2, fields, s3) ->
          let all_fields = Seplist.to_list fields in
          let all_fields_names = List.map (fun ((n0, l), c, s4, ty) -> Name.to_string (Name.strip_lskip (B.const_ref_to_name n0 false c))) all_fields in
          let field_entries = concat_str "\n" (List.map (aux all_fields_names) all_fields) in
          let terminator =
            if List.length all_fields = 0 then
              emp
            else
              from_string "\n"
          in
            field_entries ^ terminator
      | _                          -> emp
;;


    let generate_record_equality tvs o lskips_seplist =
      let eq_typ =
        if List.length tvs = 0 then
          Output.flat [
            from_string "(l : "; o; from_string ") (r :"; o;
            from_string ") : bool"
          ]
        else
          let eq_funs = List.map (fun tv ->
            let tv =
              match tv with
                | Typed_ast.Tn_A (_, tv, _) -> tv
                | _ -> assert false
            in
            let name = id Type_var tv in
            let eq_fun_name = Output.flat [name; from_string "_beq"] in
            let eq_fun_type = Output.flat [name; from_string " -> "; name; from_string " -> bool"] in
              Output.flat [
                from_string "("; eq_fun_name; from_string ": ";
                eq_fun_type; from_string ")"
              ]
            ) tvs
          in
          let eq_fun_list = concat_str " " eq_funs in
          let tvs = List.map (fun tv ->
            let tv =
              match tv with
                | Typed_ast.Tn_A (_, tv, _) -> tv
                | _ -> assert false
            in
            let name = id Type_var tv in
              Output.flat [
                from_string "{"; name; from_string ": Type}"
              ]
            ) tvs
          in
          let tv_list = concat_str " " tvs in
          let eq_type =
            Output.flat [
              eq_fun_list; from_string " (l : "; o; from_string ") (r :"; o;
              from_string ") : bool"
            ]
          in
            Output.flat [
              tv_list; from_string " "; eq_type
            ]
      in
      let rec decidable_equality_possible l =
        let l = List.map (fun (x, _, y, z) -> z) l in
          List.for_all (fun typ ->
            match typ.term with
              | _ -> true
          ) l
      in
      let l = Seplist.to_list lskips_seplist in
        if decidable_equality_possible l then
          let prefix =
            Output.flat [
              from_string "(* Definition "; o; from_string "_beq ";
              eq_typ; from_string ":=\n  "
            ]
          in
          let body = List.map (fun (name, _, _, typ) ->
            let t = src_t_to_string typ.term ^ from_string "_beq" in
            let _ = decidable_equality_tracker := OutputSet.add t !decidable_equality_tracker in
            let o = lskips_t_to_string name in
              Output.flat [
                t; from_string " ("; o; from_string " l) (";
                o; from_string " r)"
              ]) l
          in
          let f = concat_str " && " body in
            Output.flat [prefix; f; kwd ". *)"]
        else
          from_string "(* XXX: unable to produce decidable equality for type " ^ o ^ from_string ". *)"
    ;;

    let generate_case_expressions bods =
      match bods with
        | Te_opaque -> from_string "(* XXX: extracting equality for an opaque type.  Hard drive will now be formatted. *)"
        | Te_abbrev (_, src_t) -> from_string " (* XXX: internal Lem error, please report *)"
        | Te_record (_, _, name_l_src_t_lskips_seplist, _) -> from_string " (* XXX: internal Lem error, please report *)"
        | Te_variant (_, name_l_src_t_lskips_seplist) ->
            let l = Seplist.to_list name_l_src_t_lskips_seplist in
            let cases = List.map (fun ((name0, _), c_ref, y, typs) ->
              let name = B.const_ref_to_name name0 false c_ref in
              let typs = Seplist.to_list typs in
              let args = List.map (fun typ ->
                begin
                  match typ.term with
                    | Typ_app (_, vs) ->
                        let fresh_name = generate_fresh_name () in
                          (from_string fresh_name, typ.typ)
                    | Typ_var (_, t) ->
                        let fresh_name = generate_fresh_name () in
                          (from_string fresh_name, typ.typ)
                    | Typ_paren (_, t, _) ->
                        let fresh_name = generate_fresh_name () in
                          (from_string fresh_name, typ.typ)
                    | _ -> print_and_fail typ.locn "illegal type appearing in variant constructor type"
                end) typs
              in
              let arg_space = if List.length args = 0 then emp else from_string " " in
              let names = List.map fst args in
              let right_args = List.map (fun x -> from_string (generate_fresh_name ())) args in
              let right_args_list = concat_str " " right_args in
              let typs = List.map snd args in
              let names_list = concat_str " " names in
              let equality_test =
                if List.length typs = 0 then
                  from_string "true"
                else
                  let body = Util.list_mapi (fun i -> fun x ->
                      let left_name = List.nth names i in
                      let right_name = List.nth right_args i in
                      let typ = C.t_to_src_t @@ List.nth typs i in
                      let typ_name = src_t_to_string typ.term in
                      let eq_name = typ_name ^ from_string "_beq " in
                        Output.flat [
                          eq_name; left_name; from_string " "; right_name
                        ]
                    ) typs
                  in
                  let body = concat_str " && " body in
                    body
              in
              let catch_all =
                if List.length l > 1 then
                  from_string "\n        | _ => false"
                else
                  emp
              in
              let right_hand_side =
                Output.flat [
                  from_string "match r with\n        |";
                  Name.to_output Type_ctor name; arg_space; right_args_list;
                  from_string " => "; equality_test; catch_all; from_string "\n      end"
                ]
              in
                Output.flat [
                  from_string "|"; Name.to_output Type_ctor name; arg_space;
                  names_list; from_string " =>\n      "; right_hand_side;
                ]) l
            in
            let cases = concat_str "\n    " cases in
              Output.flat [
                from_string "  match l with\n    "; cases; from_string "\n  end"
              ]
    ;;

    let rec generate_coq_abbreviation_equality tvs name bod =
      match bod.term with
        | Typ_wild _ -> print_and_fail bod.locn "illegal wildcard type appearing in abbreviation type"
        | Typ_var (skips, tyvar) -> print_and_fail bod.locn "illegal type variable appearing in abbreviation type"
        | Typ_len src_nexp -> print_and_fail bod.locn "illegal vector length index appearing in abbreviation type"
        | Typ_fn (src_t, skips, src_t') -> from_string "(* XXX: equality on Typ_fn *)\n"
        | Typ_tup src_t_lskips_seplist -> from_string "(* XXX: equality on Typ_tup *)\n"
        | Typ_backend (path_id, src_t_list) -> from_string "(* XXX: equality on Typ_backend *)\n"
        | Typ_app (path_id, src_t_list) ->
            let eq_name = typ_ident_to_output path_id in
            Output.flat [
              from_string "(* Definition"; name; from_string "_beq :=";
              eq_name; from_string "_beq. *)"
            ]
        | Typ_paren (skips, src_t, skips') ->
            generate_coq_abbreviation_equality tvs name src_t
    ;;

    type variable
      = Tyvar of Output.t
      | Nvar of Output.t
    ;;

    let generate_variant_equality tvs o bods =
      let eq_typ =
        if List.length tvs = 0 then
          Output.flat [
            from_string " (l : "; o; from_string ") (r : "; o; from_string ") : bool"
          ]
        else
          let eq_funs = List.map (fun tv ->
            let tv =
              match tv with
                | Typed_ast.Tn_A (_, tyvar, _) -> Tyvar (from_string @@ Ulib.Text.to_string tyvar)
                | Typed_ast.Tn_N (_, nvar, _) -> Nvar (from_string @@ Ulib.Text.to_string nvar)
            in
            let eq_fun_name, eq_fun_type =
              match tv with
                | Tyvar name ->
                    Output.flat [
                      name; from_string "_beq"
                    ],
                    Output.flat [
                      name; from_string " -> "; name; from_string " -> bool"
                    ]
                | Nvar name ->
                    emp, emp
            in
              Output.flat [
                from_string "("; eq_fun_name; from_string ": ";
                eq_fun_type; from_string ")"
              ]
            ) tvs
          in
          let eq_fun_list = concat_str " " eq_funs in
          let tvs = List.map (fun tv ->
            match tv with
              | Typed_ast.Tn_A (_, tvar, _) ->
                let name = from_string @@ Ulib.Text.to_string tvar in
                  Output.flat [
                    from_string "{"; name; from_string ": Type}"
                  ]
              | Typed_ast.Tn_N (_, nvar, _) ->
                let name = from_string @@ Ulib.Text.to_string nvar in
                  Output.flat [
                    from_string "{"; name; from_string ": num}"
                  ]) tvs
          in
          let tv_list = concat_str " " tvs in
            Output.flat [
              from_string " "; tv_list; from_string " "; eq_fun_list;
              from_string " (l : "; o; from_string ") (r : "; o; from_string ") : bool"
            ]
      in
      let dec_eq_name =
        Output.flat [
          o; from_string "_beq"
        ]
      in
      let cases = generate_case_expressions bods in
        Output.flat [
          from_string "(* "; dec_eq_name; eq_typ;
          from_string " :=\n"; cases; from_string " *)"
        ]
    ;;

    let generate_coq_record_equality tvs name lskips_seplist =
      let o = lskips_t_to_string name in
        generate_record_equality tvs o lskips_seplist
    ;;

    let generate_coq_variant_equality lskips_seplist =
      (* 
      let l = Seplist.to_list lskips_seplist in
      let names = List.map (fun (x, y, _, z, _) -> lskips_t_to_string x) l in
      let tvs = List.map (fun (x, y, _, z, _) -> y) l in
      let bods = List.map (fun (x, y, _, z, _) -> z) l in
      let rec zip3 x y z =
        match x, y, z with
          | [], [], [] -> []
          | x::xs, y::ys, z::zs -> (x, y, z)::(zip3 xs ys zs)
          | _ -> assert false (* illegal mismatch of list lengths *)
      in
      let zipped = zip3 tvs names bods in
      let mapped = List.map (fun (x, y, z) -> generate_variant_equality x y z) zipped in
      let body = concat_str "\nwith " mapped in
        Output.flat [
          from_string "(* "; from_string "Fixpoint "; body; from_string ". *)\n" 
        ]
      *)
      emp
    ;;

    let rec is_inferrable (s : src_t) : bool =
      match s.term with
        | Typ_var _ -> true
        | Typ_app (path, src_ts) ->
            List.length src_ts = 0 || List.for_all is_inferrable src_ts
        | Typ_tup seplist ->
          let src_ts = Seplist.to_list seplist in
            List.for_all is_inferrable src_ts
        | Typ_paren (_, src_t, _) -> is_inferrable src_t
        | _ -> false
    ;;

    module DefaultMap = Map.Make (struct type t = string let compare = Pervasives.compare end)
    ;;

    let initial_default_map : string list DefaultMap.t ref =
      let d =
        DefaultMap.empty |>
        DefaultMap.add "fmap_default" ["a"; "b"] |>
        DefaultMap.add "set_default" ["a"] |>
        DefaultMap.add "list_default" ["a"]
      in
        ref d
    ;;

    let add_to_default_map k v =
      initial_default_map := DefaultMap.add k v !initial_default_map
    ;;

    let lookup_from_default_map k =
      DefaultMap.find k !initial_default_map
    ;;

    let rec def (inside_instance: bool) (callback : def list -> Output.t) (inside_module : bool) (m : def_aux) =
      match m with
      | Type_def (skips, def) ->
          let funcl =	if is_abbreviation def then
        		  type_def_abbreviation
        		else if is_record def then
        		  type_def_record
        		else
        			type_def inside_module
          in
            Output.flat [
              ws skips; funcl def;
              generate_default_values def;
            ]
      | Val_def (def) ->
          let class_constraints =val_def_get_class_constraints A.env def in
          let tv_set = val_def_get_free_tnvars A.env def in
          val_def false None (snd (Typed_ast_syntax.is_recursive_def m)) def tv_set class_constraints
      | Module (skips, (name, l), mod_binding, skips', skips'', defs, skips''') ->
        let name = lskips_t_to_output name in
        let body = callback defs in
          Output.flat [
            ws skips; from_string "Module "; name; from_string "."; ws skips'; ws skips'';
            body; from_string "\nEnd "; name; from_string "."; ws skips'''
          ]
      | Rename (skips, name, mod_binding, skips', mod_descr) -> from_string "Rename"
      | OpenImport (oi, mod_descrs) ->                  
          let (skips, can_drop) = match oi with
            | Ast.OI_import sk -> (sk, true)
            | Ast.OI_include sk -> (sk, false)
            | Ast.OI_include_import (sk1, sk2) -> (Ast.combine_lex_skips sk1 sk2, false)
            | Ast.OI_open sk -> (sk, false)
            | Ast.OI_open_import (sk1, sk2) -> (Ast.combine_lex_skips sk1 sk2, false)
          in
          let handle_mod mod_p = begin
            let mod_path = B.module_id_to_ident mod_p in
            let mod_name = Ident.get_name mod_path in
            if (mod_name |> Name.strip_lskip |> Name.to_string) = "Vector" then
               Output.flat []
            else
              let mod_name = Name.to_output Term_var mod_name in
                Output.flat [
                  ws skips; from_string "Require Import "; mod_name; from_string ".\n"
                ]
          end in
          if can_drop then emp else Output.flat (List.map handle_mod mod_descrs)
      | Indreln (skips, targets, names, cs) -> (*INDERL_TODO Only added the name declaration parameter here*)
          if in_target targets then
            let c = Seplist.to_list cs in
              clauses inside_instance c
          else
            let cs = Seplist.to_list cs in
              Output.flat [
                ws skips; clauses inside_instance cs
              ]
      | Val_spec val_spec -> from_string "\n(* [?]: removed value specification. *)\n"
      | Class (skips, skips', (name, l), tv, p, skips'', body, skips''') ->
          let name = Name.to_output Term_var name in
          let tv =
            begin
              match tv with
                | Typed_ast.Tn_A (_, tyvar, _) ->
                    from_string @@ Ulib.Text.to_string tyvar
                | Typed_ast.Tn_N (_, nvar, l) ->
                    from_string "NOT SUPPORTED"
            end
          in
          let body_notations =
            List.map (fun (skips, (name, l), const_descr_ref, ascii_rep_opt, skips', src_t) ->
              let name' = B.const_ref_to_name name true const_descr_ref in
              let notation =
                if name = name' then
                  []
                else
                  [name, name']
              in
              let name = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name')) in
                Output.flat [
                  ws skips; from_string name; from_string ":"; ws skips'; typ src_t
                ], notation
            ) body
          in
          let notations = List.flatten (List.map snd body_notations) in
          let rec generate_notations notations =
            match notations with
              | [] -> from_string ""
              | (infix, name)::xs ->
                let tail = generate_notations xs in
                let name = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name)) in
                let infix = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip infix)) in
                Output.flat [
                  from_string "Notation \" X \'"; from_string infix; from_string "\' Y\" := ("
                ; from_string name; from_string " X Y)."
                ; from_string "\n"; tail
                ]
          in
          let body = Output.concat (from_string "\n") (List.map fst body_notations) in
          Output.flat [
            ws skips; from_string "Class"; ws skips'; name; from_string " ("; tv; from_string ": Type): Type := {"
          ; ws skips''; body
          ; from_string "\n}."; ws skips'''
          ; generate_notations notations
          ]
      | Instance (skips, i_ref, inst, vals, skips') ->
        let l_unk = Ast.Unknown in
          let prefix =
            match inst with
              | (constraint_prefix_opt, skips, ident, path, src_t, skips') ->
                let tyvars, c =
                  begin
                  match constraint_prefix_opt with
                    | None -> from_string "", from_string ""
                    | Some c ->
                      begin
                      match c with
                        | Cp_forall (skips, tnvar_list, skips', constraints_opt) ->
                            let tnvars =
                              Output.concat (from_string " ") (List.map (fun t ->
                                match t with
                                  | Typed_ast.Tn_A (_, var, _) ->
                                      from_string @@ Ulib.Text.to_string var
                                  | _ ->
                                    raise (Reporting_basic.err_general true l_unk "nexps not supported in instance declarations")
                              ) tnvar_list)
                            in
                            let cs =
                              begin
                              match constraints_opt with
                                | None -> from_string ""
                                | Some cs ->
                                  match cs with
                                    | Cs_list (ident_var_seplist, skips_opt, range_seplist, skips') ->
                                      let ident_var_list = Seplist.to_list ident_var_seplist in
                                      let ident_var_list =
                                        Output.concat (from_string " ") (List.map (fun (id, var) ->
                                          let var =
                                            match var with
                                              | Typed_ast.Tn_A (_, var, _) ->
                                                  from_string @@ Ulib.Text.to_string var
                                              | _ ->
                                                raise (Reporting_basic.err_general true l_unk "nexps not supported in instance declarations") 
                                          in
                                          let ident = Name.to_output Term_var (Ident.get_name id) in
                                            Output.flat [
                                              from_string "`{"; ident; from_string " "; var; from_string "}"
                                            ]) ident_var_list)
                                      in
                                        ident_var_list
                              end
                            in
                              Output.flat [
                                ws skips; from_string "{"; tnvars; from_string ": Type}";
                              ],
                              Output.flat [
                                ws skips'; cs
                              ]
                      end
                  end
                in
                let id = Name.to_output Term_var (Ident.get_name ident) in
                let instance_id =
                  let fresh = generate_fresh_name () in
                  Output.flat [
                     from_string fresh; from_string "_"; id
                  ]
                in
                  Output.flat [
                    ws skips; instance_id; tyvars; from_string " "; c; from_string ": "; id; typ src_t
                  ]
          in
          let body =
            Output.concat (from_string "\n") (List.map (fun d -> val_def true (Some i_ref) false d Types.TNset.empty []) vals)
          in
            Output.flat [
              ws skips; from_string "Instance"; prefix; from_string ":= {";
              body;
              from_string "\n}."; ws skips'
            ]
      | Comment c ->
      	let ((def_aux, skips_opt), l, lenv) = c in
          Output.flat [
      		  from_string "(* "; def inside_instance callback inside_module def_aux; from_string " *)"
          ]
      | Lemma (skips, lemma_typ, targets, name_skips_opt, skips', e, skips'') ->
          if in_target targets then
            let name =
              match name_skips_opt with
                | None ->
                  let fresh = generate_fresh_name () in
                  Output.flat [
                    from_string " lemma_"; from_string fresh
                  ]
                | Some ((name, l), skips) -> Name.to_output Term_var name
            in
              Output.flat [
                ws skips; from_string "Lemma"; name; from_string ":"; ws skips';
                from_string "("; exp inside_instance e; from_string ": Prop)";
                ws skips''; from_string "."
              ]
          else
            from_string "(* [?]: removed lemma intended for another backend. *)"
      | Declaration declare -> from_string "" (* XXX: declarations empty for Coq backend *)
    and val_def inside_instance i_ref_opt is_recursive def tv_set class_constraints =
      begin
        let constraints =
          let body =
            Output.concat (from_string " ") (List.map (fun (path, tnvar) ->
              let name = Path.get_name path in
              let name = from_string (Ulib.Text.to_string (Name.to_rope name)) in
              let var =
                match tnvar with
                  | Types.Ty var -> from_string @@ Ulib.Text.to_string @@ Types.tnvar_to_rope tnvar
                  | _ ->
                      raise (Reporting_basic.err_general true Ast.Unknown "nexps not supported in type class constraints")
              in 
                Output.flat [
                  name; from_string " "; var
                ]
            ) class_constraints)
          in
          if List.length class_constraints = 0 then
            from_string ""
          else
            Output.flat [
              from_string "`{"; body; from_string "}"
            ]
        in
        match def with
          | Let_def (skips, targets, (p, name_map, topt, sk, e)) ->
              if in_target targets then
                let bind = (Let_val (p, topt, sk, e), Ast.Unknown) in
                let body = let_body inside_instance i_ref_opt true tv_set bind in
                let defn, ending =
                  if inside_instance then
                    from_string "", from_string ""
                  else
                    from_string "Definition", from_string "."
                  in
                    Output.flat [
                      ws skips; defn; constraints; body; ending
                    ]
              else
                ws skips ^ from_string "(* [?]: removed value definition intended for another target. *)"
          | Fun_def (skips, rec_flag, targets, funcl_skips_seplist) ->
              if in_target targets then
                let skips' = match rec_flag with FR_non_rec -> None | FR_rec sk -> sk in
                let header, ending =
                  if is_recursive then
                    if inside_instance then
                      ws skips', from_string ""
                    else
                      Output.flat [
                        from_string "Program"; ws skips'; from_string "Fixpoint"
                      ], from_string "."
                  else
                    if inside_instance then
                      from_string "", from_string ""
                    else
                      Output.flat [
                        from_string "Definition";
                      ], from_string "."
                in
                let funcls = Seplist.to_list funcl_skips_seplist in
                let bodies = List.map (funcl inside_instance i_ref_opt constraints tv_set) funcls in
                let formed = concat_str "\nwith" bodies in
                  Output.flat [
                    ws skips; header; formed; ending
                  ]
              else
                from_string "\n(* [?]: removed recursive definition intended for another target. *)"
          | _ -> from_string "\n(* [?]: removed top-level value definition. *)"
      end
    and clauses (inside_instance: bool) clause_list =
      let gather_names clause_list =
        let rec gather_names_aux buffer clauses =
          match clauses with
            | []    -> buffer
            | (Rule(_,_, _, _, _, _, _, name_lskips_annot, _, _),_)::xs ->
              let name = name_lskips_annot.term in
              let name = Name.strip_lskip name in
              if List.mem name buffer then
                gather_names_aux buffer xs
              else
                gather_names_aux (name::buffer) xs
        in
          gather_names_aux [] clause_list
      in
      let gathered = gather_names clause_list in
      (* TODO: use refs instead of names *)
      let compare_clauses_by_name name (Rule(_,_, _, _, _, _, _, name', _, _),_) =
        let name' = name'.term in
        let name' = Name.strip_lskip name' in
          Pervasives.compare name name' = 0
      in
      let indrelns =
        List.map (fun name ->
          let name_string = Name.to_string name in
          let bodies = List.filter (compare_clauses_by_name name) clause_list in
          let index_types =
            match bodies with
              | [] -> [from_string "Prop"]
              | (Rule(_,_, _, _, _, _, _, _, _, exp_list),_)::xs ->
                  List.map (fun t ->
                    Output.flat [
                      from_string "("; indreln_typ @@ C.t_to_src_t (Typed_ast.exp_to_typ t); from_string ")"
                    ]
                  ) exp_list
          in
          let bodies =
            Util.list_mapi (fun counter -> fun (Rule(name_lskips_t, skips0, skips, name_lskips_annot_list, skips', exp_opt, skips'', name_lskips_annot, c, exp_list),_) ->
              let constructor_name =
              (* Note, now that names are not optional, this code is likely unneccessary, and an extra skip is added*)
(*                match name_lskips_t_opt with
                  | None ->
                    let fresh = string_of_int counter in
                    let name = Name.to_string name in
                      Output.flat [
                        from_string name; from_string "_"; from_string fresh
                      ]
                  | Some name ->*)
                  from_string (Name.to_string (Name.strip_lskip name_lskips_t))
              in
              let antecedent =
                match exp_opt with
                  | None -> emp
                  | Some e ->
                      Output.flat [
                        from_string "("; exp inside_instance e; from_string ": Prop)"
                      ]
              in
              (* Indrel TODO This does not match variables with type annotations *)
              let bound_variables =
                concat_str " " @@ List.map (fun (QName n) ->
                  from_string (Name.to_string (Name.strip_lskip n.term))
                ) name_lskips_annot_list
              in
              let binder, binder_sep =
                match name_lskips_annot_list with
                  | [] -> emp, emp
                  | x::xs -> from_string "forall ", from_string ", "
              in
              let indices = concat_str " " @@ List.map (exp inside_instance) exp_list in
              let index_free_vars = List.map (fun t -> Types.free_vars (Typed_ast.exp_to_typ t)) exp_list in
              let index_free_vars = List.fold_right Types.TNset.union index_free_vars Types.TNset.empty in
              let relation_name = from_string (Name.to_string name) in
                Output.flat [
                  constructor_name; from_string ": ";
                  binder; bound_variables; binder_sep; antecedent; from_string " -> ";
                  relation_name; from_string " "; indices
                ], index_free_vars
            ) bodies
          in
          let free_vars = List.map (fun (x, y) -> y) bodies in
          let free_vars = Types.TNset.elements @@ List.fold_right Types.TNset.union free_vars Types.TNset.empty in
          let free_vars =
            concat_str " " @@ List.map (fun v ->
              Output.flat [
                from_string " {"; from_string (Name.to_string (Types.tnvar_to_name v)); from_string ": Type}"
              ]) free_vars
          in
          let index_types =
            Output.flat [
              concat_str " -> " index_types; from_string " -> Prop"
            ]
          in
          let bodies = concat_str "\n  | " @@ List.map (fun (x, y) -> x) bodies in
          Output.flat [
            from_string name_string; free_vars; from_string ": "; index_types; from_string " :=\n  | ";
            bodies
          ]
        ) gathered
      in
        Output.flat [
          from_string "\nInductive "; concat_str "\nand " indrelns; from_string "."
        ]
    and let_body inside_instance i_ref_opt top_level tv_set ((lb, _):letbind) =
      match lb with
        | Let_val (p, topt, skips, e) ->
            let p = def_pattern p in
            let tv_set_sep, tv_set =
              if Types.TNset.cardinal tv_set = 0 then
                let typ = Typed_ast.exp_to_typ e in
                let tv_set = Types.free_vars typ in
                  if Types.TNset.cardinal tv_set = 0 then
                    emp, tv_set
                  else
                    from_string " ", tv_set
              else
                from_string " ", tv_set
            in
            let tv_set = let_type_variables top_level tv_set in
            let topt =
              match topt with
                | None        -> emp
                | Some (s, t) ->
                    Output.flat [
                      ws s; from_string ":"; pat_typ t
                    ]
            in
            let e = exp inside_instance e in
              Output.flat [
                p; tv_set_sep; tv_set; topt; ws skips; from_string " := "; e
              ]
        | Let_fun (n, pats, typ_opt, skips, e) ->
          funcl_aux inside_instance i_ref_opt (from_string "") tv_set (n.term, pats, typ_opt, skips, e)
    and funcl_aux inside_instance i_ref_opt constraints tv_set (n, pats, typ_opt, skips, e) =
      let name_skips = Name.get_lskip n in
      let name = from_string (Name.to_string (Name.strip_lskip n)) in
      let pat_skips =
        match pats with
          | [] -> emp
          | _  -> from_string " "
      in
      let constraints_sep =
        if constraints = from_string "" then
          from_string ""
        else
          from_string " "
      in
      let tv_set_sep, tv_set =
        if inside_instance then
          from_string "", from_string ""
        else
          if Types.TNset.cardinal tv_set = 0 then
            let typ = Typed_ast.exp_to_typ e in
            let tv_set = Types.free_vars typ in
              if Types.TNset.cardinal tv_set = 0 then
                emp, let_type_variables true tv_set
              else
                from_string " ", let_type_variables true tv_set
          else
            from_string " ", let_type_variables true tv_set
      in
      let typ_opt =
        match typ_opt with
          | None -> emp
          | Some (s, t) ->
              Output.flat [
                ws s; from_string " : "; pat_typ t
              ]
      in
        Output.flat [
          ws name_skips; name; tv_set_sep; tv_set; constraints_sep; constraints; pat_skips;
          fun_pattern_list inside_instance pats; typ_opt; ws skips; from_string ":= "; exp inside_instance e
        ]
    and funcl inside_instance i_ref_opt constraints tv_set ({term = n}, c, pats, typ_opt, skips, e) =
      let n =
        if inside_instance then
          match i_ref_opt with
            | None -> B.const_ref_to_name n true c
            | Some i_ref ->
              begin
                let instance = Types.i_env_lookup Ast.Unknown A.env.i_env i_ref in
                let filtered = List.filter (fun x -> snd x = c) instance.inst_methods in
                  match filtered with
                    | x::xs -> B.const_ref_to_name n true (fst x)
                    | _   -> assert false
              end
        else
          B.const_ref_to_name n true c
      in
        funcl_aux inside_instance i_ref_opt constraints tv_set (n, pats, typ_opt, skips, e)
    and let_type_variables top_level tv_set =
      if Types.TNset.is_empty tv_set || not top_level then
        emp
      else
      let tyvars =
        List.map (fun tv -> match tv with
          | Types.Ty tv -> id Type_var (Tyvar.to_rope tv)
          | Types.Nv nv -> id Type_var (Nvar.to_rope nv)) (*TODO This may not be how the length variables should be represented, so should be checked on *)
        (Types.TNset.elements tv_set)
      in
        if List.length tyvars = 0 || not top_level then
          emp
        else
          (from_string "{") ^ (concat_str " " tyvars) ^ (from_string " : Type}")
    and coq_function_application_to_output inside_instance l id args = B.function_application_to_output l (exp inside_instance) id args
    and exp inside_instance e =
      let is_user_exp = Typed_ast_syntax.is_pp_exp e in
        match C.exp_to_term e with
          | Var v ->
              Name.to_output Term_var v
          | Backend (sk, i) ->
              ws sk ^
              Ident.to_output Term_const path_sep i
          | Lit l -> literal l
          | Do (skips, mod_descr_id, do_line_list, skips', e, skips'', type_int) -> assert false (* DPM: should have been removed by macros *)
          | App (e1, e2) ->
              let trans e = block (Typed_ast_syntax.is_pp_exp e) 0 (exp inside_instance e) in
              let sep = (break_hint_space 2) in

              let oL = begin
              (* try to strip all application and see whether there is a constant at the beginning *)
              let (e0, args) = strip_app_exp e in
                match C.exp_to_term e0 with
                  | Constant cd -> 
                    (* constant, so use special formatting *)
                    B.function_application_to_output (exp_to_locn e) trans false e cd args (use_ascii_rep_for_const cd.descr)
                  | _ -> (* no constant, so use standard one *)
                    List.map trans (e0 :: args)
              end in
              let o = Output.concat sep oL in
              block is_user_exp 0 o
          | Paren (skips, e, skips') ->
              Output.flat [
                ws skips; from_string "("; exp inside_instance e; ws skips'; from_string ")";
              ]
          | Typed (skips, e, skips', t, skips'') ->
              Output.flat [
                ws skips; from_string "("; exp inside_instance e; from_string " :"; ws skips'; typ t; ws skips''; from_string ")";
              ]
          | Tup (skips, es, skips') ->
              let tups = flat @@ Seplist.to_sep_list (exp inside_instance) (sep (from_string ", ")) es in
                Output.flat [
                  ws skips; from_string "("; tups; from_string ")"; ws skips'
                ]
          | List (skips, es, skips') ->
              let lists = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> from_string " ")) (exp inside_instance) (sep @@ from_string "; ") es in
                Output.flat [
                  ws skips; from_string "["; lists; from_string "]"; ws skips'
                ]
          | Let (skips, bind, skips', e) ->
              let body = let_body inside_instance None false Types.TNset.empty bind in
                Output.flat [
                  ws skips; from_string "let"; body; ws skips'; from_string "in "; exp inside_instance e;
                ]
          | Constant const -> 
            Output.concat emp (B.function_application_to_output (exp_to_locn e) (exp inside_instance) false e const [] (use_ascii_rep_for_const const.descr))
          | Fun (skips, ps, skips', e) ->
              let ps = fun_pattern_list inside_instance ps in
                block_hov (Typed_ast_syntax.is_pp_exp e) 2 (
                  Output.flat [
                    ws skips; from_string "fun"; ps; ws skips'; from_string "=>"; break_hint_space 0; exp inside_instance e
                  ])
          | Function _ ->
            (* DPM: should have been macro'd away *)
              print_and_fail (Typed_ast.exp_to_locn e) "illegal function in extraction, should have been previously macro'd away"
          | Set (skips, es, skips') ->
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) (exp inside_instance) (sep @@ from_string "; ") es in
            let skips =
              if skips = Typed_ast.no_lskips then
                from_string " "
              else
                ws skips
            in
              block is_user_exp 0 (
                if Seplist.is_empty es then
                  Output.flat [
                    skips; from_string "[]"
                  ]
                else
                  Output.flat [
                    skips; from_string "["; body; ws skips'; from_string "]"
                  ])
          | Begin (skips, e, skips') ->
              Output.flat [
                ws skips; from_string "(* begin block *)"; exp inside_instance e; ws skips';
                from_string "(* end block *)"
              ]
          | Record (skips, fields, skips') ->
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) (field_update inside_instance) (sep @@ from_string ";") fields in
              Output.flat [
                ws skips; from_string "{|"; body; ws skips'; from_string "|}"
              ]
          | Field (e, skips, fd) ->
            let name = field_ident_to_output fd (use_ascii_rep_for_const fd.descr) in
              Output.flat [
                from_string "("; name; ws skips; exp inside_instance e; from_string ")"
              ]
          | Recup (skips, e, skips', fields, skips'') ->
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) (field_update inside_instance) (sep @@ from_string ";") fields in
            let skips'' =
              if skips'' = Typed_ast.no_lskips then
                from_string " "
              else
                ws skips''
            in
              Output.flat [
                 ws skips; from_string "{["; exp inside_instance e; ws skips'; from_string "with"; body; skips''; from_string " ]}"
              ]
          | Case (_, skips, e, skips', cases, skips'') ->
            let body = flat @@ Seplist.to_sep_list_last Seplist.Optional (case_line inside_instance) (sep (break_hint_space 2 ^ from_string "|")) cases in
              block is_user_exp 0 (
                Output.flat [
                  ws skips; from_string "match ("; exp inside_instance e; from_string ")"; from_string " with"; ws skips';
                  break_hint_space 4; body; ws skips''; break_hint_space 0; from_string "end"
                ])
          | Infix (l, c, r) ->
              let trans e = block (Typed_ast_syntax.is_pp_exp e) 0 (exp inside_instance e) in
              let sep = (break_hint_space 0) in
              begin
                match C.exp_to_term c with
                  | Constant cd ->
                    begin
                      let pieces = B.function_application_to_output (exp_to_locn e) trans true e cd [l; r] (use_ascii_rep_for_const cd.descr) in
                      let output = Output.concat sep pieces in
                        block is_user_exp 0 output
                    end
                  | _           ->
                    begin
                      let mapped = List.map trans [l; c; r] in
                      let output = Output.concat sep mapped in
                        block is_user_exp 0 output
                    end
              end
          | If (skips, test, skips', t, skips'', f) ->
              block is_user_exp 0 (Output.flat [
                ws skips; break_hint_cut; from_string "if";
                block (Typed_ast_syntax.is_pp_exp test) 0 (exp inside_instance test);
                ws skips'; from_string "then"; break_hint_space 2;
                block (Typed_ast_syntax.is_pp_exp t) 0 (exp inside_instance t);
                ws skips''; break_hint_space 0; from_string "else"; break_hint_space 2;
                block (Typed_ast_syntax.is_pp_exp f) 0 (exp inside_instance f)
              ])
          | Quant (quant, quant_binding_list, skips, e) ->
            (* XXX: this should only appear in the context of a lemma or theorem statement,
             *      and should have been macro'd away hopefully elsewhere.
             *)
            let quant =
              match quant with
                | Ast.Q_forall _ -> from_string "forall"
                | Ast.Q_exists _ -> from_string "exists"
            in
            let bindings =
              Output.concat (from_string " ") (
                List.map (fun quant_binding ->
                  match quant_binding with
                    | Typed_ast.Qb_var name_lskips_annot ->
                      let name = name_lskips_annot.term in
                      let skip = Name.get_lskip name in
                      let name = Name.strip_lskip name in
                      let name = Ulib.Text.to_string (Name.to_rope name) in
                        Output.flat [
                          ws skip; from_string name
                        ]
                    | Typed_ast.Qb_restr (bool, skips, pat, skips', e, skips'') ->
                      let pat_out = fun_pattern pat in
                        Output.flat [
                          ws skips; pat_out; ws skips'; from_string " : ";
                          exp inside_instance e; ws skips''
                        ]
                ) quant_binding_list)
            in
              Output.flat [
                quant; bindings; from_string ","; ws skips;
                from_string "("; exp inside_instance e; from_string " : Prop)"
              ]
          | Comp_binding (_, _, _, _, _, _, _, _, _) -> from_string "(* XXX: comp binding *)"
          | Setcomp (_, _, _, _, _, _) -> from_string "(* XXX: setcomp *)"
          | Nvar_e (skips, nvar) ->
            let nvar = id Nexpr_var @@ Ulib.Text.(^^^) (r "") (Nvar.to_rope nvar) in
              Output.flat [
                ws skips; nvar
              ]
          | VectorAcc (e, skips, nexp, skips') ->
              Output.flat [
                from_string "vector_index"; exp inside_instance e; ws skips; src_nexp nexp; ws skips'
              ]
          | VectorSub (e, skips, nexp, skips', nexp', skips'') ->
              Output.flat [
                from_string "vector_slice"; exp inside_instance e; ws skips; src_nexp nexp;
                ws skips'; src_nexp nexp'; ws skips'
              ]
          | Vector (skips, es, skips') ->
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) (exp inside_instance) (sep @@ from_string "; ") es in
            let skips =
              if skips = Typed_ast.no_lskips then
                from_string " "
              else
                ws skips
            in
              block is_user_exp 0 (
                if Seplist.is_empty es then
                  Output.flat [
                    skips; from_string "[[]]]"
                  ]
                else
                  Output.flat [
                    skips; from_string "[["; body; ws skips'; from_string "]]"
                  ])
    and src_nexp n =
      match n.nterm with
        | Nexp_var (skips, nvar) ->
          let nvar = id Nexpr_var @@ Ulib.Text.(^^^) (r"") (Nvar.to_rope nvar) in
            Output.flat [
              ws skips; nvar
            ]
        | Nexp_const (skips, i) ->
            Output.flat [
              ws skips; from_string (string_of_int i)
            ]
        | Nexp_mult (nexp, skips, nexp') ->
            Output.flat [
              src_nexp nexp; ws skips; from_string "*"; src_nexp nexp'
            ]
        | Nexp_add (nexp, skips, nexp') ->
            Output.flat [
              src_nexp nexp; ws skips; from_string "+"; src_nexp nexp'
            ]
        | Nexp_paren (skips, nexp, skips') ->
            Output.flat [
              ws skips; from_string "("; src_nexp nexp; ws skips'; from_string ")"
            ]
    and case_line inside_instance (p, skips, e, _) =
        Output.flat [
          def_pattern p; ws skips; from_string "=>"; break_hint_space 2; exp inside_instance e
        ]
    and field_update inside_instance (fd, skips, e, _) =
      let name = field_ident_to_output fd (use_ascii_rep_for_const fd.descr) in
        Output.flat [
          name; ws skips; from_string ":="; exp inside_instance e
        ]
    and literal l =
      match l.term with
        | L_true skips -> ws skips ^ from_string "true"
        | L_false skips -> ws skips ^ from_string "false"
        | L_num (skips, n) -> ws skips ^ num n
        | L_string (skips, s) ->
            (* in Coq, string literals are UTF8 except doublequotes which are doubled *)
            let escaped = Str.global_replace (Str.regexp "\"") "\"\"" s in
            ws skips ^ str (Ulib.Text.of_string escaped)
        | L_unit (skips, skips') -> ws skips ^ from_string "tt" ^ ws skips'
        | L_undefined (skips, explanation) ->
          let typ = l.typ in
          let src_t = C.t_to_src_t typ in
            Output.flat [
              ws skips; default_value src_t;
              from_string " (* "; from_string explanation; from_string " *)"
            ]
    and fun_pattern_list inside_instance ps =
      let f =
        if inside_instance then
          def_pattern
        else
          fun_pattern
      in
        Output.flat [
          from_string " "; (concat_str " " @@ List.map f ps)
        ]
    and fun_pattern p =
      match p.term with
        | P_wild skips ->
          let skips =
            if skips = Typed_ast.no_lskips then
              from_string " "
            else
              ws skips
          in
          let t = C.t_to_src_t p.typ in
            Output.flat [
              skips; from_string "("; from_string "_ : "; pat_typ t; from_string ")"
            ]
        | P_var v ->
          let name = lskips_t_to_output v in
          let t = C.t_to_src_t p.typ in
            Output.flat [
              from_string "("; name; from_string " : "; pat_typ t; from_string ")"
            ]
        | P_lit l -> literal l
        | P_as (skips, p, skips', (n, l), skips'') ->
          let name = Name.to_output Term_var n in
            Output.flat [
              ws skips; fun_pattern p; ws skips'; from_string "as"; ws skips''; name
            ]
        | P_typ (skips, p, skips', t, skips'') ->
            Output.flat [
              ws skips; from_string "("; def_pattern p; ws skips'; from_string ":";
              ws skips''; pat_typ t; from_string ")"
            ]
        | P_tup (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list fun_pattern (sep @@ from_string ", ") ps in
            Output.flat [
              ws skips; from_string "("; body; ws skips'; from_string ")"
            ]
        | P_record (_, fields, _) ->
          (* DPM: should have been macro'd away *)
            print_and_fail p.locn "illegal record pattern in code extraction, should have been compiled away"
        | P_cons (p1, skips, p2) ->
            Output.flat [
              def_pattern p1; ws skips; from_string "::"; def_pattern p2
            ]
        | P_var_annot (n, t) ->
            let name = Name.to_output Term_var n in
              Output.flat [
                from_string "("; name; from_string " : "; pat_typ t; from_string ")"
              ]
        | P_list (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list_last Seplist.Optional fun_pattern (sep @@ from_string "; ") ps in
            Output.flat [
              ws skips; from_string "["; body; from_string "]"; ws skips'
            ]
        | P_paren (skips, p, skips') ->
            Output.flat [
              ws skips; from_string "("; fun_pattern p; ws skips'; from_string ")"
            ]
        | P_const(cd, ps) ->
            let oL = B.pattern_application_to_output fun_pattern cd ps (use_ascii_rep_for_const cd.descr) in
            concat emp oL
        | P_backend(sk, i, _, ps) ->
            ws sk ^
            Ident.to_output Term_const path_sep i ^
            concat texspace (List.map fun_pattern ps)
        | P_num_add ((name, l), skips, skips', k) ->
            let succs = Output.flat @@ Util.replicate k (from_string "S (") in
            let close = Output.flat @@ Util.replicate k (from_string ")") in
            let name = lskips_t_to_output name in
              Output.flat [
                ws skips; succs; name; close
              ]
        | _ -> from_string "(* XXX: todo *)"
    and def_pattern p =
      match p.term with
        | P_wild skips ->
          let skips =
            if skips = Typed_ast.no_lskips then
              from_string " "
            else
              ws skips
          in
            Output.flat [
              skips; from_string "_"
            ]
        | P_var v -> Name.to_output Term_var v
        | P_lit l -> literal l
        | P_as (skips, p, skips', (n, l), skips'') ->
          let name = Name.to_output Term_var n in
            Output.flat [
              ws skips; def_pattern p; ws skips'; from_string "as"; ws skips'; name
            ]
        | P_typ (skips, p, _, t, skips') ->
            (* DPM: type restriction not allowed in Coq *)
            Output.flat [
              ws skips; def_pattern p; ws skips'
            ]
        | P_tup (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list def_pattern (sep @@ from_string ", ") ps in
            Output.flat [
              ws skips; from_string "("; body; from_string ")"; ws skips'
            ]
        | P_record (_, fields, _) ->
            (* DPM: should have been macro'd away *)
            print_and_fail p.locn "illegal record pattern in code extraction, should have been compiled away"
        | P_cons (p1, skips, p2) ->
            Output.flat [
              def_pattern p1; ws skips; from_string "::"; def_pattern p2
            ]
        | P_var_annot (n, t) ->
          (* DPM: type restriction not allowed in Coq *)
            Name.to_output Term_var n
        | P_list (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list_last Seplist.Optional def_pattern (sep @@ from_string "; ") ps in
            Output.flat [
              ws skips; from_string "["; body; from_string "]"; ws skips'
            ]
        | P_paren (skips, p, skips') ->
            Output.flat [
              from_string "("; ws skips; def_pattern p; ws skips'; from_string ")"
            ]
        | P_const(cd, ps) ->
            let oL = B.pattern_application_to_output def_pattern cd ps (use_ascii_rep_for_const cd.descr) in
            concat emp oL
        | P_backend(sk, i, _, ps) ->
            ws sk ^
            Ident.to_output Term_const path_sep i ^
            concat texspace (List.map def_pattern ps)
        | P_num_add ((name, l), skips, skips', k) ->
            let succs = Output.flat @@ Util.replicate k (from_string "S (") in
            let close = Output.flat @@ Util.replicate k (from_string ")") in
            let name = lskips_t_to_output name in
              Output.flat [
                ws skips; succs; name; close
              ]
        | _ -> from_string "(* XXX: todo *)"
    and type_def_abbreviation def =
    	match Seplist.hd def with
    		| ((n, _), tyvars, _, Te_abbrev (skips, t),_) ->
    				let name = Name.to_output Type_ctor n in
            let tyvars' = type_def_type_variables tyvars in
    				let tyvar_sep = if List.length tyvars = 0 then emp else from_string " " in
            let body = abbreviation_typ t in
            let equality = generate_coq_abbreviation_equality tyvars name t in
              Output.flat [
    						from_string "Definition"; name; tyvar_sep; tyvars';
                from_string " : Type :="; ws skips; body; from_string ".\n";
                (*equality*)
    					]
    		| _ -> from_string "(* Internal Lem error, please report. *)"
    and abbreviation_typ t =
      match t.term with
        | Typ_wild skips -> ws skips ^ from_string "_"
        | Typ_var (skips, v) -> id Type_var @@ Ulib.Text.(^^^) (r"") (Tyvar.to_rope v)
        | Typ_fn (t1, skips, t2) -> abbreviation_typ t1 ^ ws skips ^ kwd "->" ^ abbreviation_typ t2
        | Typ_tup ts ->
            let body = flat @@ Seplist.to_sep_list abbreviation_typ (sep @@ from_string "*") ts in
              from_string "(" ^ body ^ from_string ") % type"
        | Typ_app (p, ts) ->
          let args = concat_str " " @@ List.map abbreviation_typ ts in
          let (name_list, name) = Ident.to_name_list (B.type_id_to_ident p) in
          let arg_sep = if List.length ts > 1 then from_string " " else emp in
            Output.flat [
              kwd @@ Ulib.Text.to_string (Name.to_rope name); arg_sep; args
            ]
        | Typ_paren(skips, t, skips') ->
            Output.flat [
              ws skips; from_string "("; abbreviation_typ t; from_string ")"; ws skips'
            ]
        | Typ_len nexp -> src_nexp nexp
    and type_def_record def =
    	match Seplist.hd def with
      	| (n, tyvars, _, (Te_record (skips, skips', fields, skips'') as r),_) ->
            let (n', _) = n in
            let name = Name.to_output Type_ctor n' in
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun x -> emp)) field (sep @@ from_string ";") fields in
      	    let tyvars' = type_def_type_variables tyvars in
            let tyvar_sep = if List.length tyvars = 0 then emp else from_string " " in
            let boolean_equality = generate_coq_record_equality tyvars n fields in
      			  Output.flat [
                from_string "Record"; name; tyvar_sep; tyvars'; from_string " : Type";
                ws skips; from_string ":="; ws skips'; from_string "{";
                body; ws skips''; from_string "}.\n";
                generate_coq_record_update_notation r;
      			  ]
        | _ -> from_string "(* Internal Lem error, please report. *)"
    and type_def inside_module defs =
      let body = flat @@ Seplist.to_sep_list type_def' (sep @@ from_string "with") defs in
      let boolean_equality = generate_coq_variant_equality defs in
      let head =
        if inside_module then
          from_string "Parameter"
        else
          from_string "Inductive"
      in
        Output.flat [
          head; body; from_string ".\n";
          boolean_equality
        ]
    and type_def' ((n0, l), ty_vars, t_path, ty, _) =
      let n = B.type_path_to_name n0 t_path in 
      let name = Name.to_output Type_ctor n in
      let ty_vars =
        List.map (
          function
            | Typed_ast.Tn_A (_, tyvar, _) -> Tyvar (from_string @@ Ulib.Text.to_string tyvar)
            | Typed_ast.Tn_N (_, nvar, _) -> Nvar (from_string @@ Ulib.Text.to_string nvar)
          ) ty_vars
      in
        match ty with
          | Te_opaque ->
              Output.flat [
                inductive ty_vars n; from_string ":= "
              ]
          | _ ->
            Output.flat [
              inductive ty_vars n; tyexp name ty_vars ty
            ]
    and inductive ty_vars name =
      let ty_var_sep = if List.length ty_vars = 0 then emp else from_string " " in
      let ty_vars = inductive_type_variables ty_vars in
      let name = Name.to_output Type_ctor name in
        Output.flat [
          name; ty_var_sep; ty_vars; from_string " : Type "
        ]
    and inductive_type_variables vars =
      let mapped = List.map (fun v ->
          match v with
            | Tyvar x ->
              Output.flat [
                from_string "{"; x; from_string " : Type}"
              ]
            | Nvar x ->
              Output.flat [
                from_string "{"; x; from_string " : num}"
              ]) vars
      in
        concat_str " " mapped
    and tyexp name ty_vars =
      function
        | Te_opaque -> emp
        | Te_abbrev (skips, t) -> ws skips ^ tyexp_abbreviation t
        | Te_record (skips, _, fields, skips') -> ws skips ^ tyexp_record fields ^ ws skips'
        | Te_variant (skips, ctors) ->
          let body = flat @@ Seplist.to_sep_list_first Seplist.Optional (constructor name ty_vars) (sep @@ from_string "|") ctors in
            Output.flat [
              from_string ":="; ws skips; body
            ]
    and constructor ind_name ty_vars ((name0, _), c_ref, skips, args) =
      let ctor_name = B.const_ref_to_name name0 false c_ref in
      let ctor_name = Name.to_output Type_ctor ctor_name in
      let body = flat @@ Seplist.to_sep_list abbreviation_typ (sep @@ from_string "-> ") args in
      let tail = Output.flat [from_string "->"; ind_name ] in
        if Seplist.length args = 0 then
          Output.flat [
            ctor_name; from_string ":"; ws skips; ind_name
          ]
        else
          Output.flat [
            ctor_name; from_string ":"; ws skips; body; from_string " "; tail
          ]
    and tyexp_abbreviation t = from_string "(* tyexp_abbreviation *)"
    and tyexp_record fields = from_string "(* tyexp_record *)"
    and pat_typ t =
      match t.term with
        | Typ_wild skips -> ws skips ^ from_string "_"
        | Typ_var (skips, v) -> ws skips ^ (id Type_var @@ Ulib.Text.(^^^) (r"") (Tyvar.to_rope v))
        | Typ_fn (t1, skips, t2) ->
            if skips = Typed_ast.no_lskips then
              pat_typ t1 ^ from_string " -> " ^ ws skips ^ pat_typ t2
            else
              pat_typ t1 ^ from_string " ->" ^ ws skips ^ pat_typ t2
        | Typ_tup ts ->
            let body = flat @@ Seplist.to_sep_list pat_typ (sep @@ from_string "*") ts in
              from_string "(" ^ body ^ from_string ") % type"
        | Typ_app (p, ts) ->                    
            Output.flat [
              typ_ident_to_output p; from_string " ";
              concat_str " " (List.map pat_typ ts)
            ]
        | Typ_paren(skips, t, skips') ->
            ws skips ^ from_string "(" ^ pat_typ t ^ ws skips' ^ from_string ")"
        | Typ_len nexp -> src_nexp nexp
    and typ t =
    	match t.term with
      	| Typ_wild skips -> ws skips ^ from_string "_"
      	| Typ_var (skips, v) -> id Type_var @@ Ulib.Text.(^^^) (r"") (Tyvar.to_rope v)
      	| Typ_fn (t1, skips, t2) -> typ t1 ^ ws skips ^ kwd "->" ^ typ t2
      	| Typ_tup ts ->
      			let body = flat @@ Seplist.to_sep_list typ (sep @@ from_string "*") ts in
          		from_string "(" ^ body ^ from_string ") % type"
      	| Typ_app (p, ts) ->
           typ_ident_to_output p
      	| Typ_paren (skips, t, skips') ->
          	ws skips ^ from_string "(" ^ typ t ^ from_string ")" ^ ws skips'
        | Typ_len nexp -> src_nexp nexp
    and type_def_type_variables tvs =
      match tvs with
        | [] -> emp
        | [Typed_ast.Tn_A tv] -> from_string "{" ^ tyvar tv ^ from_string ": Type}"
        | tvs ->
          let mapped = List.map (fun t ->
            match t with
              | Typed_ast.Tn_A (_, tv, _) ->
                let tv = from_string @@ Ulib.Text.to_string tv in
                  Output.flat [
                    from_string "{"; tv; from_string ": Type}"
                  ]
              | Typed_ast.Tn_N nv ->
                  Output.flat [
                    from_string "{"; from_string "nv: num}"
                  ]) tvs
          in
            Output.flat [
              from_string " "; concat_str " " mapped
            ]
    and indreln_typ t =
      match t.term with
        | Typ_wild skips -> ws skips ^ from_string "_"
        | Typ_var (skips, v) -> id Type_var @@ Ulib.Text.(^^^) (r"") (Tyvar.to_rope v)
        | Typ_fn (t1, skips, t2) ->
          begin
            match t2.term with
              | Typ_app (p, []) ->
                if p.descr = Path.boolpath then
                  indreln_typ t1 ^ ws skips ^ from_string "->" ^ from_string "Prop"
                else
                  indreln_typ t1 ^ ws skips ^ from_string "->" ^ indreln_typ t2
              | _ ->
                indreln_typ t1 ^ ws skips ^ from_string "->" ^ indreln_typ t2
          end
        | Typ_tup ts ->
            let body = flat @@ Seplist.to_sep_list indreln_typ (sep @@ from_string "*") ts in
              from_string "(" ^ body ^ from_string ") % type"
        | Typ_app (p, ts) ->
          let args = concat_str " " @@ List.map indreln_typ ts in
          let args_space = if List.length ts = 1 then from_string " " else emp in
            Output.flat [
              typ_ident_to_output p; args_space; args
            ]
        | Typ_paren(skips, t, skips') ->
            ws skips ^ from_string "(" ^ indreln_typ t ^ from_string ")" ^ ws skips'
        | Typ_len nexp -> src_nexp nexp
    and field_typ t =
      match t.term with
        | Typ_wild skips -> ws skips ^ from_string "_"
        | Typ_var (skips, v) -> id Type_var @@ Ulib.Text.(^^^) (r"") (Tyvar.to_rope v)
        | Typ_fn (t1, skips, t2) -> field_typ t1 ^ ws skips ^ from_string "->" ^ field_typ t2
        | Typ_tup ts ->
            let body = flat @@ Seplist.to_sep_list typ (sep @@ from_string "*") ts in
              from_string "(" ^ body ^ from_string ") % type"
        | Typ_app (p, ts) ->
          let args = concat_str " " @@ List.map field_typ ts in
          let args_space = if List.length ts = 1 then from_string " " else emp in
            Output.flat [
              typ_ident_to_output p; args_space; args
            ]
        | Typ_paren(skips, t, skips') ->
            ws skips ^ from_string "(" ^ typ t ^ from_string ")" ^ ws skips'
        | Typ_len nexp -> src_nexp nexp
    and field ((n, _), f_ref, skips, t) =
      Output.flat [
          Name.to_output Term_field (B.const_ref_to_name n false f_ref); 
          from_string ":"; ws skips; field_typ t
      ]
    and generate_default_value_texp (t: texp) =
      match t with
        | Te_opaque -> from_string "DAEMON"
        | Te_abbrev (_, src_t) -> default_value src_t
        | Te_record (_, _, seplist, _) ->
            let fields = Seplist.to_list seplist in
            let mapped = List.map (fun ((name, _), _, _, src_t) ->
              let o = lskips_t_to_output name in
              let s = default_value src_t in
                Output.flat [
                  o; from_string " := "; s
                ]
              ) fields
            in
            let fields = concat_str "; " mapped in
              Output.flat [
                from_string "{| "; fields; from_string " |}"
              ]
        | Te_variant (_, seplist) ->
            (match Seplist.to_list seplist with
              | []    -> assert false (* empty type in default value generation, should this be allowed? *)
              | x::xs ->
                let ((name, _), _, _, src_ts) = x in
                  let ys = Seplist.to_list src_ts in
                  let mapped = List.map default_value ys in
                  let mapped = concat_str " " mapped in
                  let o = lskips_t_to_output name in
                    Output.flat [
                      o; from_string " "; mapped
                    ])
      and generate_default_value ((name, _), tnvar_list, _, t, name_sect_opt) : Output.t =
        let o = lskips_t_to_output name in
        let tnvar_list_sep =
          if List.length tnvar_list = 0 then
            emp
          else
            from_string " "
        in
        let tnvar_list' = type_def_type_variables tnvar_list in
        let default = generate_default_value_texp t in
        let mapped = concat_str " " @@ List.map (fun x ->
          match x with
            | Typed_ast.Tn_A (_, x, _)->
              let x = Ulib.Text.to_string x in
              Output.flat [
                from_string "("; from_string x; from_string ":=";
                from_string x; from_string ")"
              ]
              | _ -> from_string "BUG"
          ) tnvar_list
        in
          Output.flat [
            from_string "Definition "; o; from_string "_default";
            tnvar_list'; tnvar_list_sep; from_string ": "; o;
            from_string " := "; default; from_string " ";
            mapped; from_string "."
          ]
      and default_value (s : src_t) : Output.t =
        match s.term with
          | Typ_wild _ -> from_string "DAEMON"
          | Typ_var _ -> from_string "DAEMON"
          | Typ_len _ -> from_string "len_var_default"
          | Typ_tup seplist ->
              let src_ts = Seplist.to_list seplist in
              let mapped = List.map default_value src_ts in
                Output.flat [
                  from_string "("; concat_str ", " mapped; from_string ")"
                ]
          | Typ_app (path, src_ts) ->
              if List.length src_ts = 0 || List.for_all is_inferrable src_ts then
                  Output.flat [
                    from_string (Name.to_string (Name.strip_lskip (Ident.get_name (B.type_id_to_ident path)))); 
                    from_string "_default"
                  ]
              else
                from_string "DAEMON"
          | Typ_paren (_, src_t, _) -> default_value src_t
          | Typ_fn (dom, _, rng) ->
              let v = generate_fresh_name () in
                Output.flat [
                  from_string "(fun ("; from_string v; from_string " : "; pat_typ dom;
                  from_string ") => "; default_value rng; from_string ")"
                ]
      and generate_default_values ts : Output.t =
        let ts = Seplist.to_list ts in
        let mapped = List.map generate_default_value ts in
          concat_str "\n" mapped
      ;;
end
;;


module CdsetE = Util.ExtraSet(Types.Cdset)

module CoqBackend (A : sig val avoid : var_avoid_f option;; val env : env end) =
  struct

    let rec defs inside_instance inside_module (ds : def list) =
      	List.fold_right (fun (((d, s), l, lenv):def) y ->
          let ue = add_def_entities (Target_no_ident Target_coq) true empty_used_entities ((d,s),l,lenv) in

          let module C = CoqBackendAux (
             struct
                let avoid = A.avoid;;
                let env = {A.env with local_env = lenv};;
		            let ascii_rep_set = CdsetE.from_list ue.used_consts
             end) in
          let callback = defs false true in
          match s with
            | None   -> C.def inside_instance callback inside_module d ^ y
            | Some s -> C.def inside_instance callback inside_module d ^ ws s ^ y
      	) ds emp

    let coq_defs ((ds : def list), end_lex_skips) =
    	to_rope (r"\"") lex_skip need_space @@ defs false false ds ^ ws end_lex_skips
    ;;

end
