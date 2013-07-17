open Types
open Typed_ast

let raise_error = Ident.raise_error


type pat_env = (t * Ast.l) Nfmap.t
let empty_pat_env = Nfmap.empty

type lex_env = (t * Ast.l) Nfmap.t
let empty_lex_env = Nfmap.empty


(* As we process definitions, we need to keep track of the type definitions
 * (type_defs), class instance definitions (instance list Pfmap.t) and
 * function/value/module/field (env) definitions we encounter. *)
type defn_ctxt = {
  all_tdefs : type_defs; 
  new_tdefs : type_defs;
  all_instances : instance list Pfmap.t;
  new_instances : instance list Pfmap.t;
  cur_env : env;
  new_defs : env;
  lemmata_labels : NameSet.t;
}

(* Update the new and cumulative environment with new
 * function/value/module/field/path definitions according to set and select *)
let ctxt_add (select : env -> 'a Nfmap.t) (set : env -> 'a Nfmap.t -> env) 
      (ctxt : defn_ctxt) (m : Name.t * 'a)
      : defn_ctxt =
  { ctxt with 
        cur_env = set ctxt.cur_env (Nfmap.insert (select ctxt.cur_env) m);
        new_defs = set ctxt.new_defs (Nfmap.insert (select ctxt.new_defs) m); } 

(* Update new and cumulative enviroments with a new module definition, after
 * first checking that its name doesn't clash with another module definition in
 * the same definition sequence.  It can have the same name as another module
 * globally. *)
let add_m_to_ctxt (l : Ast.l) (ctxt : defn_ctxt) (k : Name.lskips_t) (v : mod_descr)
      : defn_ctxt = 
  let k = Name.strip_lskip k in
    if Nfmap.in_dom k ctxt.new_defs.m_env then
      raise_error l "duplicate module definition" Name.pp k
    else
      ctxt_add 
        (fun x -> x.m_env) 
        (fun x y -> { x with m_env = y }) 
        ctxt 
        (k,v)

(* Add a new type definition to the global and local contexts *)
let add_d_to_ctxt (ctxt : defn_ctxt) (p : Path.t) (d : tc_def) =
  { ctxt with all_tdefs = Pfmap.insert ctxt.all_tdefs (p,d);
              new_tdefs = Pfmap.insert ctxt.new_tdefs (p,d) }

(* Support for maps from paths to lists of things *)
let insert_pfmap_list (m : 'a list Pfmap.t) (k : Path.t) (v : 'a) 
      : 'a list Pfmap.t =
  match Pfmap.apply m k with
    | None -> Pfmap.insert m (k,[v])
    | Some(l) -> Pfmap.insert m (k,v::l)

(* Add a lemma name to the context *)
let add_lemma_to_ctxt (ctxt : defn_ctxt) (n : Name.t)  
      : defn_ctxt =
  { ctxt with lemmata_labels = NameSet.add n ctxt.lemmata_labels; }

(* Add a new instance the the new instances and the global instances *)
let add_instance_to_ctxt (ctxt : defn_ctxt) (p : Path.t) (i : instance) 
      : defn_ctxt =
  { ctxt with all_instances = insert_pfmap_list ctxt.all_instances p i;
              new_instances = insert_pfmap_list ctxt.new_instances p i; }

let add_let_defs_to_ctxt 
      (* The path of the enclosing module *)
      (mod_path : Name.t list)
      (ctxt : defn_ctxt)
      (* The type and length variables that were generalised for this definition *)
      (tnvars : Types.tnvar list) 
      (* The class constraints that the definition's type variables must satisfy
      *) 
      (constraints : (Path.t * Types.tnvar) list)
      (* The length constraints that the definition's length variables must satisfy *) 
      (lconstraints : Types.range list)
      (* The status for just this definition, must be either K_let or
       * K_target(false, ts), and if it is K_target, there must be a preceding
       * K_val *)
      (env_tag : env_tag) 
      (* If this definition should be inlined for a target, give that target,
       * the parameters and the body *)
      (substitution : (Targetset.t * ((Name.t,unit) annot list * exp)) option)
      (l_env : lex_env) 
      : defn_ctxt =
  let add_subst =
    match substitution with
      | None -> (fun c -> c)
      | Some(ts,s) ->
          (fun c -> 
             { c with substitutions = 
                 Targetset.fold
                   (fun t r -> Targetmap.insert r (t,s))
                   ts 
                   c.substitutions 
             })
  in
  let new_env =
    Nfmap.map
      (fun n (t,l) ->
        match Nfmap.apply ctxt.new_defs.v_env n with
          | None ->
              Val(add_subst
                    { const_binding = Path.mk_path mod_path n;
                      const_tparams = tnvars;
                      const_class = constraints;
                      const_ranges = lconstraints;
                      const_type = t;
                      spec_l = l;
                      env_tag = env_tag;
                      substitutions = Targetmap.empty })
          | Some(Val(c)) ->
              (* The definition is already in the context.  Here we just assume
               * it is compatible with the existing definition, having
               * previously checked it. *) 
              let tag =
                match (c.env_tag, env_tag) with
                  | (K_val, K_val) | (K_let,K_let) | ((K_method|K_instance),_) 
                  | (_,(K_method|K_instance)) | (K_let, K_val) | (K_target _, K_val) -> 
                      assert false
                  | (K_val, K_let) -> K_target(true, Targetset.empty)
                  | (K_val, K_target(letdef,targets)) -> 
                      K_target(letdef,targets)
                  | (K_let, K_target(_,targets)) -> K_target(true,targets)
                  | (K_target(_,targets),K_let) -> K_target(true,targets)
                  | (K_target(letdef1,targets1), K_target(letdef2,targets2)) ->
                      K_target(letdef1||letdef2, 
                               Targetset.union targets1 targets2)
              in
                Val(add_subst { c with env_tag = tag })
          | _ -> assert false)
      l_env
  in
  { ctxt with 
        cur_env = 
          { ctxt.cur_env with v_env = Nfmap.union ctxt.cur_env.v_env new_env };
        new_defs = 
          { ctxt.new_defs with 
                v_env = Nfmap.union ctxt.new_defs.v_env new_env } }
