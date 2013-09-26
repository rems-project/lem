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
  all_instances : Types.i_env;

  (* All class instances defined in this sequence of definitions *)
  new_instances : Types.i_env;

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

val add_d_to_ctxt : defn_ctxt -> Path.t -> Types.tc_def -> defn_ctxt
val add_p_to_ctxt : defn_ctxt -> Name.t * (Path.t * Ast.l) -> defn_ctxt
val add_f_to_ctxt : defn_ctxt -> Name.t * Types.const_descr_ref -> defn_ctxt
val add_v_to_ctxt : defn_ctxt -> Name.t * Types.const_descr_ref -> defn_ctxt
val add_m_to_ctxt : Ast.l -> defn_ctxt -> Name.t -> Typed_ast.mod_descr -> defn_ctxt
val add_instance_to_ctxt : defn_ctxt -> Types.instance -> defn_ctxt
val add_lemma_to_ctxt : defn_ctxt -> Name.t -> defn_ctxt

val defn_ctxt_get_cur_env : defn_ctxt -> Typed_ast.env

