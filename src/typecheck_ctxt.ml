open Types
open Typed_ast

type defn_ctxt = { 
  all_tdefs : type_defs; 
  ctxt_c_env : c_env;
  new_tdefs : Path.t list;
  all_instances : i_env;
  new_instances : i_env;
  cur_env : local_env;
  new_defs : local_env;
  lemmata_labels : NameSet.t; 
}



(* Update the new and cumulative environment with new
 * function/value/module/field/path definitions according to set and select.
 * The types of set and select are quite general. However, they are only used
 * to select and set the appropriate fields of the local environment. No fancy
 * operations are performed. With this contract, the function ctxt really only
 * adds a module, constant, field, ... to the context.
 *)
let ctxt_add (select : local_env -> 'a Nfmap.t) (set : local_env -> 'a Nfmap.t -> local_env) 
      (ctxt : defn_ctxt) (m : Name.t * 'a)
      : defn_ctxt =
  { ctxt with 
        cur_env = set ctxt.cur_env (Nfmap.insert (select ctxt.cur_env) m);
        new_defs = set ctxt.new_defs (Nfmap.insert (select ctxt.new_defs) m); } 


(* Add a new type definition to the global and local contexts *)
let add_d_to_ctxt (ctxt : defn_ctxt) (p : Path.t) (d : tc_def) =
  { ctxt with all_tdefs = Pfmap.insert ctxt.all_tdefs (p,d);
              new_tdefs = p :: ctxt.new_tdefs }


let defn_ctxt_get_cur_env (d : defn_ctxt) : env =
  { local_env = d.cur_env; Typed_ast.c_env = d.ctxt_c_env; t_env = d.all_tdefs; i_env = d.all_instances }


(* adds a type to p_env *)
let add_p_to_ctxt ctxt ((n:Name.t), ((ty_p:Path.t), (ty_l:Ast.l))) =
   if Nfmap.in_dom n ctxt.new_defs.p_env then
     raise (Reporting_basic.err_type_pp ty_l "duplicate type definition" Name.pp n)
   else
     ctxt_add (fun x -> x.p_env) (fun x y -> { x with p_env = y }) ctxt (n, (ty_p, ty_l))

(* adds a field to f_env *)
let add_f_to_ctxt ctxt ((n:Name.t), (r:const_descr_ref)) =
     ctxt_add (fun x -> x.f_env) (fun x y -> { x with f_env = y }) ctxt (n, r)

(* adds a constant to v_env *)
let add_v_to_ctxt ctxt ((n:Name.t), (r:const_descr_ref)) =
     ctxt_add (fun x -> x.v_env) (fun x y -> { x with v_env = y }) ctxt (n, r)

(* Update new and cumulative enviroments with a new module definition, after
 * first checking that its name doesn't clash with another module definition in
 * the same definition sequence.  It can have the same name as another module
 * globally. *)
let add_m_to_ctxt (l : Ast.l) (ctxt : defn_ctxt) (k : Name.t) (v : mod_descr)
      : defn_ctxt = 
    if Nfmap.in_dom k ctxt.new_defs.m_env then
      raise (Reporting_basic.err_type_pp l "duplicate module definition" Name.pp k)
    else
      ctxt_add 
        (fun x -> x.m_env) 
        (fun x y -> { x with m_env = y }) 
        ctxt 
        (k,v)

(* Add a lemma name to the context *)
let add_lemma_to_ctxt (ctxt : defn_ctxt) (n : Name.t)  
      : defn_ctxt =
  { ctxt with lemmata_labels = NameSet.add n ctxt.lemmata_labels; }

(* Add a new instance the the new instances and the global instances *)
let add_instance_to_ctxt (ctxt : defn_ctxt) (i : instance) 
      : defn_ctxt =
  { ctxt with all_instances = i_env_add ctxt.all_instances i;
              new_instances = i_env_add ctxt.new_instances i; }

let ctxt_c_env_set_target_rep l (ctxt : defn_ctxt) (c : const_descr_ref) (targ : Target.non_ident_target) rep = begin
  let c_descr = c_env_lookup l ctxt.ctxt_c_env c in
  let old_rep = Target.Targetmap.apply c_descr.target_rep targ in
  
  let c_descr' = {c_descr with target_rep = Target.Targetmap.insert c_descr.target_rep (targ, rep);
                               const_targets = Target.Targetset.add targ c_descr.const_targets} in
  let ctxt' = {ctxt with ctxt_c_env = c_env_update ctxt.ctxt_c_env c c_descr'} in

  (ctxt', old_rep)
end


