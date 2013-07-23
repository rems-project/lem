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
  all_instances : instance list Pfmap.t;
  new_instances : instance list Pfmap.t;
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
