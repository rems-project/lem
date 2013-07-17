val raise_error :
  Ast.l -> string -> (Format.formatter -> 'a -> unit) -> 'a -> 'b

type pat_env = (Types.t * Ast.l) Typed_ast.Nfmap.t
val empty_pat_env : 'a Typed_ast.Nfmap.t


(* Non-top level binders map to a type, not a type scheme, method or constructor
 * *) 
type lex_env = (Types.t * Ast.l) Typed_ast.Nfmap.t
val empty_lex_env : 'a Typed_ast.Nfmap.t

type defn_ctxt = { 
  (* All type definitions ever seen *) 
  all_tdefs : Types.type_defs;
  (* All types defined in this sequence of definitions *)
  new_tdefs : Types.type_defs;

  (* All class instances ever seen *)
  all_instances : Types.instance list Types.Pfmap.t;
  (* All class instances defined in this sequence of definitions *)
  new_instances : Types.instance list Types.Pfmap.t;

  (* The current value/function/module/field/type_name environment *)
  cur_env : Typed_ast.env;
  (* The value/function/module/field/type_names defined in this sequence of
   * definitions *)
  new_defs : Typed_ast.env;

  (* The names of all assertions / lemmata defined. Used only to avoid using names multiple times. *)
  lemmata_labels : Typed_ast.NameSet.t; }

val ctxt_add :
  (Typed_ast.env -> 'a Typed_ast.Nfmap.t) ->
  (Typed_ast.env -> 'a Typed_ast.Nfmap.t -> Typed_ast.env) ->
  defn_ctxt -> Name.t * 'a -> defn_ctxt
val add_m_to_ctxt :
  Ast.l -> defn_ctxt -> Name.lskips_t -> Typed_ast.mod_descr -> defn_ctxt
val add_d_to_ctxt : defn_ctxt -> Path.t -> Types.tc_def -> defn_ctxt
val insert_pfmap_list :
  'a list Types.Pfmap.t -> Path.t -> 'a -> 'a list Types.Pfmap.t
val add_lemma_to_ctxt : defn_ctxt -> Name.t -> defn_ctxt
val add_instance_to_ctxt : defn_ctxt -> Path.t -> Types.instance -> defn_ctxt
val add_let_defs_to_ctxt :
  Name.t list ->
  defn_ctxt ->
  Types.tnvar list ->
  (Path.t * Types.tnvar) list ->
  Types.range list ->
  Typed_ast.env_tag ->
  (Target.Targetset.t *
   ((Name.t, unit) Typed_ast.annot list * Typed_ast.exp))
  option -> lex_env -> defn_ctxt
