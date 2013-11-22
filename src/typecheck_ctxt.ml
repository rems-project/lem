open Types
open Typed_ast

type defn_ctxt = { 
  all_tdefs : type_defs; 
  ctxt_c_env : c_env;
  ctxt_e_env : mod_descr Pfmap.t;
  all_instances : i_env;

  lemmata_labels : NameSet.t; 
  ctxt_mod_target_rep: Typed_ast.mod_target_rep Target.Targetmap.t;
  ctxt_mod_in_output : bool;

  cur_env : local_env;
  new_defs : local_env;
  export_env : local_env;

  new_tdefs : Path.t list;
  new_instances : instance_ref list;
}



(* Update the new and cumulative environment with new
 * function/value/module/field/path definitions according to set and select.
 * The types of set and select are quite general. However, they are only used
 * to select and set the appropriate fields of the local environment. No fancy
 * operations are performed. With this contract, the function ctxt really only
 * adds a module, constant, field, ... to the context.
 *)
let ctxt_local_update (select : local_env -> 'a Nfmap.t) (set : local_env -> 'a Nfmap.t -> local_env) 
      (ctxt : defn_ctxt) (f : 'a Nfmap.t -> 'a Nfmap.t)
      : defn_ctxt =
  { ctxt with 
        cur_env = set ctxt.cur_env (f (select ctxt.cur_env));
        new_defs = set ctxt.new_defs (f (select ctxt.new_defs));
        export_env = set ctxt.export_env (f (select ctxt.export_env)); } 

let ctxt_local_add select set ctxt m =
  ctxt_local_update select set ctxt (fun s -> Nfmap.insert s m)

(* Add a new type definition to the global and local contexts *)
let add_d_to_ctxt (ctxt : defn_ctxt) (p : Path.t) (d : tc_def) =
  { ctxt with all_tdefs = Pfmap.insert ctxt.all_tdefs (p,d);
              new_tdefs = p :: ctxt.new_tdefs }


let defn_ctxt_to_env (d : defn_ctxt) : env =
  { local_env = d.cur_env; Typed_ast.c_env = d.ctxt_c_env; t_env = d.all_tdefs; i_env = d.all_instances; e_env = d.ctxt_e_env }


(* adds a type to p_env *)
let add_p_to_ctxt ctxt ((n:Name.t), ((ty_p:Path.t), (ty_l:Ast.l))) =
   if Nfmap.in_dom n ctxt.new_defs.p_env then
     raise (Reporting_basic.err_type_pp ty_l "duplicate type definition" Name.pp n)
   else
     ctxt_local_add (fun x -> x.p_env) (fun x y -> { x with p_env = y }) ctxt (n, (ty_p, ty_l))

(* adds a field to f_env *)
let add_f_to_ctxt ctxt ((n:Name.t), (r:const_descr_ref)) =
     ctxt_local_add (fun x -> x.f_env) (fun x y -> { x with f_env = y }) ctxt (n, r)

(* adds a constant to v_env *)
let add_v_to_ctxt ctxt ((n:Name.t), (r:const_descr_ref)) =
     ctxt_local_add (fun x -> x.v_env) (fun x y -> { x with v_env = y }) ctxt (n, r)

let union_v_ctxt ctxt map  =
  ctxt_local_update (fun x -> x.v_env) (fun x y -> { x with v_env = y }) 
                    ctxt (fun m -> Nfmap.union m map) 


(* Update new and cumulative enviroments with a new module definition, after
 * first checking that its name doesn't clash with another module definition in
 * the same definition sequence.  It can have the same name as another module
 * globally. *)
let add_m_to_ctxt (l : Ast.l) (ctxt : defn_ctxt) (k : Name.t) (v : mod_descr)
      : defn_ctxt = 
    if Nfmap.in_dom k ctxt.new_defs.m_env then
      raise (Reporting_basic.err_type_pp l "duplicate module definition" Name.pp k)
    else
      ctxt_local_add 
        (fun x -> x.m_env) 
        (fun x y -> { x with m_env = y }) 
        {ctxt with ctxt_e_env = Pfmap.insert ctxt.ctxt_e_env (v.mod_binding, v)}
        (k,v.mod_binding)

let add_m_alias_to_ctxt (l : Ast.l) (ctxt : defn_ctxt) (k : Name.t) (m : Path.t)
      : defn_ctxt = 
    if Nfmap.in_dom k ctxt.new_defs.m_env then
      raise (Reporting_basic.err_type_pp l "duplicate module definition" Name.pp k)
    else
      ctxt_local_add 
        (fun x -> x.m_env) 
        (fun x y -> { x with m_env = y }) 
        ctxt
        (k,m)

(* Add a lemma name to the context *)
let add_lemma_to_ctxt (ctxt : defn_ctxt) (n : Name.t)  
      : defn_ctxt =
  { ctxt with lemmata_labels = NameSet.add n ctxt.lemmata_labels; }

(* Add a new instance the the new instances and the global instances *)
let add_instance_to_ctxt (ctxt : defn_ctxt) (i : instance)  : (defn_ctxt * instance_ref) =
  let (all_instances', new_ref) = i_env_add ctxt.all_instances i in
  let ctxt' = { ctxt with all_instances = all_instances';
                          new_instances = new_ref::ctxt.new_instances; } in
  (ctxt', new_ref)

let ctxt_c_env_set_target_rep l (ctxt : defn_ctxt) (c : const_descr_ref) (targ : Target.non_ident_target) rep = begin
  let c_descr = c_env_lookup l ctxt.ctxt_c_env c in

  let old_rep_opt = Target.Targetmap.apply c_descr.target_rep targ in
  let _ =  match  old_rep_opt with
      | None -> (* no representation present before, so OK *) ()
      | Some old_rep -> if Typed_ast_syntax.const_target_rep_allow_override old_rep then () else begin
          let loc_s = Reporting_basic.loc_to_string true (Typed_ast_syntax.const_target_rep_to_loc old_rep) in
          let msg = Format.sprintf 
                      "a %s target representation for '%s' has already been given at\n    %s" 
                      (Target.non_ident_target_to_string targ) (Path.to_string c_descr.const_binding) loc_s in
          raise (Reporting_basic.err_type l msg)
        end
  in 
  let c_descr' = {c_descr with target_rep = Target.Targetmap.insert c_descr.target_rep (targ, rep);
                               const_targets = Target.Targetset.add targ c_descr.const_targets} in
  let ctxt' = {ctxt with ctxt_c_env = c_env_update ctxt.ctxt_c_env c c_descr'} in

  (ctxt', old_rep_opt)
end

let ctxt_all_tdefs_set_target_rep l (ctxt : defn_ctxt) (p : Path.t) (targ : Target.non_ident_target) rep = begin
  let td = match Pfmap.apply ctxt.all_tdefs p with
            | Some(Tc_type(td)) -> td 
            | _ -> raise (Reporting_basic.err_general true l "invariant in checking type broken") in
  let old_rep = Target.Targetmap.apply td.type_target_rep targ in
  
  let td' = {td with type_target_rep = Target.Targetmap.insert td.type_target_rep (targ, rep)} in
  let ctxt' = {ctxt with all_tdefs = Pfmap.insert ctxt.all_tdefs (p, Tc_type td') } in
  (ctxt', old_rep)
end



let ctxt_begin_submodule ctxt =
    { ctxt with new_defs = empty_local_env;
                export_env = empty_local_env;
                new_tdefs = [];
                new_instances = [];
                ctxt_mod_target_rep = Target.Targetmap.empty; } 


let ctxt_end_submodule l ctxt_before mod_path n ctxt =
  let ctxt' =
     {ctxt with new_defs = ctxt_before.new_defs; 
                export_env = ctxt_before.export_env;
                cur_env = ctxt_before.cur_env;
                new_tdefs = ctxt_before.new_tdefs;
                new_instances = ctxt_before.new_instances;
                ctxt_mod_target_rep = ctxt_before.ctxt_mod_target_rep } in
  add_m_to_ctxt l ctxt' n { mod_binding = Path.mk_path mod_path n; mod_env = ctxt.export_env; mod_target_rep = ctxt.ctxt_mod_target_rep; mod_in_output = ctxt.ctxt_mod_in_output; mod_filename = None }

