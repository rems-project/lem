open Types
open Typed_ast

type pat_env = (t * Ast.l) Nfmap.t
let empty_pat_env = Nfmap.empty

type lex_env = (t * Ast.l) Nfmap.t
let empty_lex_env = Nfmap.empty


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
