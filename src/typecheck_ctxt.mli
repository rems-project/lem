
type pat_env = (Types.t * Ast.l) Typed_ast.Nfmap.t
val empty_pat_env : 'a Typed_ast.Nfmap.t


(* Non-top level binders map to a type, not a type scheme, method or constructor
 * *) 
type lex_env = (Types.t * Ast.l) Typed_ast.Nfmap.t
val empty_lex_env : 'a Typed_ast.Nfmap.t


(* As we process definitions, we need to keep track of the type definitions
 * (type_defs), class instance definitions (instance list Pfmap.t) and
 * function/value/module/field (env) definitions we encounter. *)
type defn_ctxt = { 
  (* All type definitions ever seen *) 
  all_tdefs : Types.type_defs; 

  (* The global c_env *)
  ctxt_c_env : Typed_ast.c_env;

  (* All types defined in this sequence of definitions *)
  new_tdefs : Path.t list;

  (* All class instances ever seen *)
  all_instances : Types.instance list Types.Pfmap.t;
  (* All class instances defined in this sequence of definitions *)
  new_instances : Types.instance list Types.Pfmap.t;

  (* The current value/function/module/field/type_name environment *)
  cur_env : Typed_ast.local_env;

  (* The value/function/module/field/type_names defined in this sequence of
   * definitions *)
  new_defs : Typed_ast.local_env;

  (* The names of all assertions / lemmata defined. Used only to avoid using names multiple times. *)
  lemmata_labels : Typed_ast.NameSet.t; 
}

val ctxt_add :
  (Typed_ast.local_env -> 'a Typed_ast.Nfmap.t) ->
  (Typed_ast.local_env -> 'a Typed_ast.Nfmap.t -> Typed_ast.local_env) ->
  defn_ctxt -> Name.t * 'a -> defn_ctxt
