(* As we process definitions, we need to keep track of the type definitions
 * (type_defs), class instance definitions (instance list Pfmap.t) and
 * function/value/module/field (env) definitions we encounter. *)
type defn_ctxt = { 
  (* All type definitions ever seen *) 
  all_tdefs : Types.type_defs; 

  (* The global c_env *)
  ctxt_c_env : Typed_ast.c_env;

  (* The global e_env (module environment) *)
  ctxt_e_env : Typed_ast.mod_descr Types.Pfmap.t;

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

(** A definition context contains amoung other things an environment split up over several fields.
    This functions extracts this environment. *)
val defn_ctxt_to_env : defn_ctxt -> Typed_ast.env

(** [ctxt_c_env_set_target_rep l ctxt c targ new_rep] updates the target-representation of
    constant [c] for target [targ] in context [ctxt] to [new_rep]. This results into a new
    environment. If an representation was already stored (and is now overridden), it is returned as well. *)
val ctxt_c_env_set_target_rep : Ast.l -> defn_ctxt -> Typed_ast.const_descr_ref -> Target.non_ident_target ->
           Typed_ast.const_target_rep -> defn_ctxt * Typed_ast.const_target_rep option
