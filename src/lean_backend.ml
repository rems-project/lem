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
(*          Brian Campbell, University of Edinburgh                       *)
(*          Shaked Flur, University of Cambridge                          *)
(*          Thomas Bauereiss, University of Cambridge                     *)
(*          Stephen Kell, University of Cambridge                         *)
(*          Thomas Williams                                               *)
(*          Lars Hupel                                                    *)
(*          Basile Clement                                                *)
(*                                                                        *)
(*  The Lem sources are copyright 2010-2025                               *)
(*  by the authors above and Institut National de Recherche en            *)
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
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(*                        Lem                                             *)
(*                                                                        *)
(*  Lean 4 backend                                                        *)
(*                                                                        *)
(*  Translates Lem definitions into Lean 4 syntax. Uses the shared        *)
(*  Backend_common infrastructure for identifier resolution and target    *)
(*  representation handling.                                               *)
(*                                                                        *)
(*  Key design decisions (the reasons are in doc/lean-backend/DESIGN.md): *)
(*  - The text is laid out by the backend's own passes (normalize_layout, *)
(*    Lean_layout.reflow); Lem's block formatting is not used             *)
(*  - UTF-8 output uses Meta_utf8 to avoid double-encoding (×, →, etc.)  *)
(*  - Constructors are exported via 'export TypeName (Ctor1 Ctor2 ...)'   *)
(*    after each inductive definition                                     *)
(*  - Class methods are brought into scope via 'open ClassName'           *)
(*  - Mutual inductives with heterogeneous parameter counts use indexed   *)
(*    types (parameters become indices with Type 1 universe)              *)
(*  - Target-specific class methods ({hol}, {coq}, etc.) are filtered     *)
(*    from both class and instance definitions                            *)
(*  - BEq/Ord are derived structurally, with OCaml's comparison order;    *)
(*    a function-typed field compares down to the closure, which fails    *)
(*    loudly, as OCaml's compare does                                     *)
(*  - Inhabited instances are DERIVED per constructor (bounded with       *)
(*    [Inhabited tv] where a type parameter is consumed); underivable     *)
(*    types get NO instance (fail-closed)                                 *)
(*  - EVERY failure site (failwith-mapped constants, L_undefined          *)
(*    literals) emits axiom-free failwithI (mirroring OCaml's raise);     *)
(*    tyvar-typed sites thread [Inhabited tv] binders onto the enclosing  *)
(*    def's signature (monotone over the call graph); no path emits a     *)
(*    `sorry`                                                             *)
(*                                                                        *)
(**************************************************************************)

open Output
open Typed_ast
open Typed_ast_syntax
open Target
open Types

let r = Ulib.Text.of_latin1

let print_and_fail l s =
  raise (Reporting_basic.err_general true l s)
;;

(* String-literal escaping for Lean output. Bytes 0x80-0xFF pass
   through RAW, deliberately: lem's lexer only admits UTF-8 source, so
   such bytes arrive here exclusively as parts of multi-byte UTF-8
   sequences, and Lean source is UTF-8 — escaping the bytes
   individually as \xHH would DECODE-SHIFT the text (Lean's \xHH is a
   Unicode scalar, not a byte). Control bytes below 0x20, which Lean
   literals cannot carry raw reliably, are hex-escaped. Paired with
   lean_char_escape below. *)
let lean_string_escape s =
  let buf = Buffer.create (String.length s) in
  String.iter (fun c -> match c with
    | '\\' -> Buffer.add_string buf "\\\\"
    | '"' -> Buffer.add_string buf "\\\""
    | '\n' -> Buffer.add_string buf "\\n"
    | '\t' -> Buffer.add_string buf "\\t"
    | '\r' -> Buffer.add_string buf "\\r"
    | c when Char.code c < 0x20 -> Buffer.add_string buf (Printf.sprintf "\\x%02x" (Char.code c))
    | c -> Buffer.add_char buf c
  ) s;
  Buffer.contents buf
;;

(* Char-literal escaping for Lean output: OCaml's Char.escaped
   emits DECIMAL escapes ('\200'), which are invalid Lean. Mirror
   Char.escaped for the cases it got right (ASCII printables +
   named controls) and emit Lean hex escapes for the rest. A lem char
   is a byte; bytes 0x80-0xFF map to the corresponding Unicode scalar
   (the latin1 embedding, '\xc8' = U+00C8) — the same convention as
   Ulib.Text.of_latin1 on the OCaml side of this backend. *)
let lean_char_escape c =
  match c with
  | '\\' -> "\\\\"
  | '\'' -> "\\'"
  | '"' -> "\\\""
  | '\n' -> "\\n"
  | '\t' -> "\\t"
  | '\r' -> "\\r"
  | c when Char.code c >= 0x20 && Char.code c < 0x7f -> String.make 1 c
  | c -> Printf.sprintf "\\x%02x" (Char.code c)
;;

(* Lean 4 syntax keywords that cannot be used as bare identifiers.
   When these appear as local variable names, they're escaped with «» guillemets. *)
let lean_syntax_keywords = [
  "def"; "class"; "instance"; "where"; "let"; "match"; "if"; "then"; "else";
  "do"; "return"; "import"; "open"; "namespace"; "structure"; "inductive";
  "theorem"; "example"; "variable"; "section"; "end"; "mutual"; "partial";
  "noncomputable"; "unsafe"; "private"; "protected"; "abbrev"; "fun"; "forall";
  "by"; "have"; "show"; "with"; "at"; "in"; "for"; "macro"; "syntax";
  "deriving"; "extends"; "set_option"; "attribute"; "meta"; "catch";
  "break"; "continue"; "try"; "finally"; "unless"; "suffices";
  "nomatch"; "nofun"; "coinductive"; "axiom"; "opaque"; "universe";
  "scoped"; "local"; "public"; "nonrec"; "omit";
  (* tokens that are a Lean parse error when emitted bare (each
     probe-verified) *)
  "from"; "termination_by"; "decreasing_by"; "elab"; "macro_rules"; "elab_rules";
  "initialize"; "builtin_initialize"; "declare_syntax_cat"; "register_option";
  "include"; "exposed";
  "notation"; "prefix"; "postfix"; "infixl"; "infixr"; "infix";
  "none"; "some"; "true"; "false"; "default";
  "this"; "rfl"; "calc"; "decide"; "sorry";
  "pure"; "get"; "set"; "throw"; "panic"; "admit"; "trivial";
  "lem_if";  (* LemLib's Bool-conditional token *)
  (* Lean 4.32.2 additions (toolchain move, scripts/lean_keyword_probe.sh) *)
  "builtin_cbv_simproc"; "builtin_cbv_simproc_decl"; "cbv_eval"; "cbv_simproc"; "cbv_simproc_decl"; "deprecated_module"; "deprecated_syntax"; "idbg"; "inferInstanceAs"; "register_sym_dsimp"; "register_sym_simp"; "unlock_limits";
  (* every identifier-shaped core-grammar token that fails as a binder on
     the pinned toolchain (linksem's `matches` was one);
     derived and checked by scripts/lean_keyword_probe.sh, which fails if
     this list or library/lean_constants misses one. *)
  "add_decl_doc"; "assert_not_exists"; "assert_not_imported"; "bif";
  "binder_predicate"; "builtin_dsimproc"; "builtin_dsimproc_decl";
  "builtin_grind_propagator"; "builtin_simproc"; "builtin_simproc_decl";
  "by_elab"; "coinductive_fixpoint"; "dbg_trace";
  "declare_bitwise_int_theorems"; "declare_bitwise_uint_theorems";
  "declare_int_theorems"; "declare_simp_like_tactic";
  "declare_uint_theorems"; "docs_to_verso"; "dsimproc"; "dsimproc_decl";
  "eval_prec"; "eval_prio"; "exists"; "export"; "generalizing";
  "grind_annotated"; "grind_pattern"; "grind_propagator"; "haveI"; "hiding";
  "include_str"; "inductive_fixpoint"; "init_grind_norm"; "init_quot";
  "leading_parser"; "let_delayed"; "let_expr"; "let_fun"; "letI"; "let_tmp";
  "logNamedError"; "logNamedErrorAt"; "logNamedWarning"; "logNamedWarningAt";
  "matches"; "match_expr"; "max_prec"; "mod_cast"; "mut"; "nat_lit";
  "no_index"; "norm_cast_add_elim"; "partial_fixpoint"; "Prop";
  "recommended_spelling"; "register_error_explanation";
  "register_tactic_tag"; "renaming"; "repeat"; "run_cmd"; "run_elab";
  "run_meta"; "seal"; "set_library_suggestions"; "show_term";
  "show_term_elab"; "simproc"; "simproc_decl"; "Sort"; "StateRefT";
  "tactic_alt"; "tactic_extension"; "tactic_name"; "tactic_tag";
  "throwNamedError"; "throwNamedErrorAt"; "trailing_parser"; "Type";
  "unif_hint"; "unseal"; "until"; "using"; "while"; "without_expected_type";
  "with_weak_namespace"
]

(* Supply transform: a threaded VALUE is
   either a synthesized variable (a draw result, a threaded call's or
   control form's joined value) or a pure/compound rendering. Keeping the
   variable NAME lets the application renderer receive real `Var`
   expressions for threaded arguments instead of a fragile substitution
   memo (identifier-form target reps rebuild the argument nodes). *)
type lean_sval = SVar of string | SPure of Output.t
let lean_sv_out = function SVar n -> Output.meta_utf8 n | SPure o -> o
(* Derived Inhabited instances: the process-global census of the
   Inhabited instances this backend has
   emitted, keyed by type Path (modules are processed in dependency order
   within one lem invocation, so earlier types' instances are visible to
   later derivations — "cross-type dependencies resolve through the
   emitted instances themselves", design note
   doc/notes/2026-08-20_arc8-inhabited-threading-design.md rule 4).
   Each emitted instance is recorded as the list of type-parameter
   POSITIONS that carry an [Inhabited _] bound; [] = unconditional.
   Inh_none records a type whose derivation FAILED: fail-closed, NO
   instance and NO fallback of any kind was emitted — any backend-visible
   Inhabited demand on such a type is a generation-time error (see
   inhabited_demand_check). *)
type inh_status =
  | Inh_instances of int list list
  | Inh_none
(* The per-type tier-2 Inhabited derivation PLAN, computed by
   lean_inhabited_prepass (in declaration order) and only RENDERED at
   emission time. Needed because the main emission walks definitions
   with fold_right — side effects run last-to-first (see the
   lean_reader_prepass / St.mutual_records precedent) — so census
   population cannot be interleaved with emission. *)
type inh_plan =
  | Plan_variant of (int * string list) list
      (* usable constructor indices (into the Te_variant ctor list) with
         their [Inhabited tv] bound sets, in emission order: first at
         default priority, rest (priority := low) *)
  | Plan_record of string list  (* all fields derivable; bound set *)
  | Plan_none                   (* fail-closed: NO instance, no fallback *)

(* ===== The backend analysis-state module =====

   EVERY module-level mutable cell OF LEAN_BACKEND.ML lives HERE — one
   declaration site, a stated lifetime class and invariant per field.
   (Two cells live outside this file by interface necessity and are
   documented at their homes: Backend_common.on_cr_simple_applied — the
   per-file callback this backend registers at lean_defs entry — and
   process_file.ml's pre-call module-name write into St.current_module_name;
   threading both through the Backend.Make signature is TODO item 6.)

   LIFETIME CLASSES:
     [file]        reset at every lean_defs entry (St.reset_per_file);
                   meaningful only within one output file's emission.
     [invocation]  grows monotonically across the modules of ONE lem
                   invocation (lem processes modules in dependency
                   order, so earlier modules' facts must stay visible
                   to later ones: census, threading, reader lifting,
                   mutual-record accumulation, the reader-param cache).
                   Reset only by St.reset_invocation.
     [render]      save/restore-scoped around a single definition's
                   rendering (Fun.protect at every write site); at its
                   neutral value between definitions.

   REENTRANCY: emission is still effectful (the upstream-inherited
   fold_right skeleton), but the whole mutable surface is resettable in
   one call: St.reset_invocation () gives a fresh backend within one
   process. *)
(* Derived-size census entry (mechanism comment at lean_size_shape
   below). *)
type size_status =
  | Size_fn of string     (* derived: the Lean name of the type (module-qualified for lem submodules) *)
  | Size_none of string   (* not derived: the reason, for the refusal message *)

module St = struct
  (* [file] Type namespace names that need 'open' in the auxiliary file. *)
  let auxiliary_opens : string list ref = ref []
  (* [file] Current namespace nesting, for qualified open names. *)
  let namespace_stack : string list ref = ref []
  (* [invocation] Record types that ended up in mutual blocks — rendered
     as inductives, not structures. Record construction ({..}) and field
     projection (.field) don't work for these; use constructor syntax and
     pattern matching instead. Accumulates across files so cross-file
     record updates on mutual-block records are detected. *)
  let mutual_records : Path.t list ref = ref []
  (* [file] Import module names — emitted at the top of the file before
     any other content. *)
  let collected_imports : string list ref = ref []
  (* [file] Locally-defined module names of the current file (Module
     definitions): namespaces, not separate files — never imports. *)
  let local_modules : string list ref = ref []
  (* [file] Fully-qualified paths of nested modules needing 'open' at
     file level (Lean's 'open' inside a namespace is scoped, so nested
     module opens are deferred to the enclosing top-level scope). *)
  let deferred_opens : string list ref = ref []
  (* [file] Set by process_file.ml before each lean_defs call — used for
     namespace wrapping (a pre-call side channel no other backend needs;
     TODO item 6). *)
  let current_module_name : string ref = ref ""
  (* [invocation] The Inhabited-instance census (see the inh_status
     comment above). *)
  let inhabited_census : (Path.t * (string * inh_status)) list ref = ref []
  (* [invocation] Per-type tier-2 derivation plans (see inh_plan above). *)
  let inhabited_tier2_plans : (Path.t * inh_plan) list ref = ref []
  (* [render] When true, isEqual outputs propositional = instead of BEq
     ==. Set during indreln antecedent processing where Prop is needed
     (function types lack BEq; indreln antecedents live in Prop). *)
  let prop_equality : bool ref = ref false
  (* [file] Deferred abbrev definitions for types with TYR_subst target
     reps — collected during type processing, drained at the end of
     lean_defs after all definitions complete. *)
  let pending_abbrevs : Output.t list ref = ref []
  (* [render] const_descr_ref -> type-parameter names for polymorphic
     indreln: set during antecedent rendering so exp inserts type params
     for self-references in premises. *)
  let indreln_params : (Types.const_descr_ref * string) list ref = ref []
  (* [invocation] Reader lifting (declare {lean} reader val): crefs of
     lifted defs — a def is lifted if it (transitively) uses a reader
     constant or a lifted def. Grows monotonically (dependency order:
     callees registered before callers). *)
  let reader_lifted : Types.Cdset.t ref = ref Types.Cdset.empty
  (* [render] Set while rendering a lifted def so the three def-assembly
     sites emit the reader binder. *)
  let reader_binder : bool ref = ref false
  (* [invocation] Instance-implicit readers (declare {lean} reader val r
     = instance `Cls.field`; mechanism comment at lean_ireader_projection):
     def cref -> the instance readers it binds, in the GLOBAL reader
     order (lean_ireader_get_readers). A def is a member if it
     (transitively) reads an instance reader, calls a consumer of one, or
     calls a member. Grown to a fixpoint by lean_ireader_prepass; persists
     across modules (the reader_lifted precedent). *)
  let ireader_lifted : Types.const_descr_ref list Types.Cdmap.t ref = ref Types.Cdmap.empty
  (* [render] The instance readers whose `[Cls]` binders are in scope for
     the definition being rendered (global reader order). [] = none: a
     read of an instance reader, or a reference to a member/consumer,
     rendered here is the fail-closed ireader_scope_check error. *)
  let ireader_binder : Types.const_descr_ref list ref = ref []
  (* [invocation] Cache of the (cref, projection, class) instance-reader
     list computed from the whole constant environment (stable within an
     invocation; the reader_params_cache discipline). *)
  let ireader_cache : (Types.const_descr_ref * string * string) list option ref = ref None
  (* [render] The [Inhabited tv] instance-implicit binders for the
     def group being rendered (tyvar names in parameter-declaration
     order, from the threading census failwith_threaded below). *)
  let inhabited_binder : string list ref = ref []
  (* [render] Fuel emission (declare {lean} fuel val f = `sentinel`):
     the sentinel text while rendering a fuel'd def's clause (consumed
     by funcl_aux: rename to worker, add the Nat counter binder, wrap the
     body). *)
  let fuel_emit : string option ref = ref None
  (* [render] All fuel'd defs of the block being rendered (one entry for
     a plain fuel'd def; every member for a fuel'd mutual block —
     all-or-none). Self- and cross-member calls rewrite to
     '(worker lemFuel)'. *)
  let fuel_workers : (Types.const_descr_ref * string) list ref = ref []
  (* [invocation] Fuel lifting: the set of
     defs that (transitively) reach a fuel'd constant or a
     `declare {lean} fuel_consumer val` — every one takes the ambient fuel
     as an instance-implicit `[LemFuel]` binder. Grown to a fixpoint by
     lean_fuel_prepass; persists across modules (the reader_lifted
     precedent). *)
  let fuel_lifted : Types.Cdset.t ref = ref Types.Cdset.empty
  (* [render] Set while rendering a fuel-lifted def (incl. every fuel'd
     worker/wrapper), so the def-assembly sites emit `[LemFuel]` and
     references to fuel-lifted constants are in scope (fuel_scope_check). *)
  let fuel_binder : bool ref = ref false
  (* [file] Fuel-measure obligations (declare {lean} fuel_measure val):
     the generated `f_measure_sufficient`
     theorem statements of this module's measured functions, collected
     while the main body renders (defs folds last-to-first, so in reverse
     declaration order) and emitted into the module's `_auxiliary.lean`
     — lem's own home for prover-side obligations — behind an import of
     the hand-written proofs module `<Module>_lemMeasureProofs`. *)
  let measure_obligations : Output.t list ref = ref []
  (* [file] Point-free `function` tails (mechanism comment at
     lean_hoist_tail_binders): for every
     measured or structural definition whose trailing `function` (or
     `fun`) binders were hoisted into its head, the hoisted binder names
     in order. Read while the fuel'd worker and its `_zero` lemma render:
     the sentinel is written in lem at the head's ORIGINAL codomain (a
     function type), so it is applied to these binders. *)
  let tail_hoisted : (Types.const_descr_ref * string list) list ref = ref []
  (* [render] The hoisted binders of the fuel'd definition being rendered
     (from tail_hoisted; [] for every other definition). *)
  let tail_sentinel_args : string list ref = ref []
  (* [invocation] Derived-size census (mechanism comment at
     lean_size_shape): every generated type path of
     the invocation -> whether the backend emits `t.lemSize` for it (with
     the Lean name a measure's `lemSize x` resolves to) or why not. Filled
     by lean_size_prepass over every typechecked module; read by the
     measure renderer. *)
  let size_census : (Path.t * size_status) list ref = ref []
  (* [render] reader_seed (declare {lean} reader_seed val f): while
     rendering a seed-marked def's body, the per-reader association
     (injected reader binder name -> the seed def's own parameter name)
     that OVERRIDES the injected reader parameter name at every
     injection site within (lexically-scoped seeding, not dynamic
     rebinding). With N declared readers a seed def's first N
     parameters are the seeds, positionally in the GLOBAL SORTED reader
     order — the one order lean_reader_get_params fixes for every
     lifted binder and consumer stub. None = not inside a seed def. *)
  let reader_seed_param : (string * string) list option ref = ref None
  (* [invocation] Cache of the (cref, param name) reader list computed
     from the whole constant environment (stable within an invocation). *)
  let reader_params_cache : (Types.const_descr_ref * string) list option ref = ref None
  (* [invocation] Supply lifting (declare {lean} supply val): crefs of
     supply-lifted defs — a def is lifted if it (transitively) draws
     from a supply constant or calls a lifted def. Grows monotonically
     (dependency order), the reader_lifted precedent. *)
  let supply_lifted : Types.Cdset.t ref = ref Types.Cdset.empty
  (* [invocation] Threading arity per supply-liftable cref: the number
     of clause parameters AFTER which the threaded result pair appears.
     Call sites must apply exactly this many arguments — linear supply
     threading has no partial-application repair (guards G-bare /
     G-arity), so under- and over-application are generation-time
     errors, never silent shape drift. *)
  let supply_arity : int Types.Cdmap.t ref = ref Types.Cdmap.empty
  (* [invocation] Cache of the (cref, binder name) supply list (sorted
     by binder name, the reader_params_cache discipline). *)
  let supply_params_cache : (Types.const_descr_ref * string) list option ref = ref None
  (* [render] Set while rendering a supply-lifted def: the def-assembly
     sites emit the supply binder(s), transform the result type to the
     value×supply pair, and thread the body (supply_block). *)
  let supply_binder : bool ref = ref false
  (* [render] Counter for names synthesized by the supply transform
     (_lemSupplyV<n> values / _lemSupplyS<n> states — deliberately NOT
     '_lemSupply_<x>', which is the binder namespace keyed by supply
     constant names; the reserved-binder prefix '_lemSupply' covers
     both). Reset at each supply_block entry. *)
  let supply_name_counter = ref 0
  (* [render] Set while the supply transform renders the HEAD constant
     of a threaded call: suppresses the fail-closed net in exp (which
     otherwise rejects any supply / supply-lifted constant reached by
     ordinary, non-threaded emission). *)
  let supply_head_ok : bool ref = ref false
  (* [render] True while rendering a definition emitted only as a BLOCK
     COMMENT (a def whose Lean target uses an inline/target_rep — the
     `Comment` def form). Fail-closed generation-time errors (e.g. the
     set-comprehension rejection) must not fire for such dead text; they
     emit an inert placeholder instead. *)
  let rendering_comment = ref false
  (* [invocation] Unique suffixes for the `_lemIfTailN` continuations
     (let-bound inside one expression, so uniqueness is only needed within
     it; the counter is never reused within an invocation). *)
  let if_tail_counter = ref 0
  (* [file] The type paths of the type_def group being emitted. *)
  let current_type_block : Path.t list ref = ref []
  (* [render] Type-variable renames for the value definition being
     rendered (lean_tyvar_renames_for; mechanism comment there): Lem
     name -> Lean binder name. Empty between definitions. *)
  let tyvar_renames : (string * string) list ref = ref []
  (* [invocation] Comparison-binder demands per generated definition
     (lean_cmp_prepass; mechanism comment there): cref -> (Lean class,
     type-variable name) list. Grows across the modules of one invocation
     in dependency order, like reader_lifted. *)
  let lean_cmp_bounds : (Types.const_descr_ref, (string * string) list) Hashtbl.t = Hashtbl.create 256
  (* [invocation] Threaded-def census: cref -> ([Inhabited]-bound
     type-parameter positions (indices into const_tparams, for call-site
     propagation), bound tyvar names in parameter-declaration order (for
     signature rendering)). Persists across modules (dependency order —
     the reader_lifted precedent). *)
  let failwith_threaded : (int list * string list) Types.Cdmap.t ref = ref Types.Cdmap.empty
  (* [invocation] Synthesized-name counter (generate_fresh_name: x<n>). *)
  let fresh_name_counter = ref 0
  (* [file] The source comments already emitted, by physical identity.
     Transformations (pattern compilation above all) copy a skip list into
     several generated nodes; the comment is the same value in each copy,
     and is emitted once, at its first position. *)
  let emitted_comments : Ast.ml_comment list ref = ref []

  (* Reset the [file]-lifetime fields — called at every lean_defs entry.
     (current_module_name and local_modules are not cleared here: both
     are unconditionally re-SET before use on every file — the module
     name by process_file.ml before the call, local_modules by the
     pre-collection in lean_defs itself.) *)
  let reset_per_file () =
    auxiliary_opens := [];
    namespace_stack := [];
    collected_imports := [];
    pending_abbrevs := [];
    deferred_opens := [];
    measure_obligations := [];
    tail_hoisted := [];
    emitted_comments := [];
    current_type_block := []

  (* Full reset — the reentrancy hook: a second lem invocation in
     one process starts from a fresh backend. Not called on the normal
     one-invocation path. *)
  let reset_invocation () =
    reset_per_file ();
    mutual_records := [];
    local_modules := [];
    current_module_name := "";
    inhabited_census := [];
    inhabited_tier2_plans := [];
    prop_equality := false;
    indreln_params := [];
    reader_lifted := Types.Cdset.empty;
    reader_binder := false;
    ireader_lifted := Types.Cdmap.empty;
    ireader_binder := [];
    ireader_cache := None;
    inhabited_binder := [];
    fuel_emit := None;
    fuel_workers := [];
    fuel_lifted := Types.Cdset.empty;
    fuel_binder := false;
    tail_sentinel_args := [];
    reader_seed_param := None;
    reader_params_cache := None;
    supply_lifted := Types.Cdset.empty;
    supply_arity := Types.Cdmap.empty;
    supply_params_cache := None;
    supply_binder := false;
    supply_name_counter := 0;
    supply_head_ok := false;
    rendering_comment := false;
    failwith_threaded := Types.Cdmap.empty;
    size_census := [];
    fresh_name_counter := 0;
    if_tail_counter := 0;
    tyvar_renames := [];
    Hashtbl.reset lean_cmp_bounds

  (* Warning-32 suppression for the reentrancy hook (no in-tree caller
     yet by design). *)
  let _ = reset_invocation
end

(* Location of a clause group's first clause's body — plumbed into the
   fail-closed guards below so refusals name WHERE, not just what
   (Reporting_basic threads it into the message). *)
let locn_of_clause_group g =
  match g with
  | (_, _, _, _, _, e) :: _ -> Typed_ast.exp_to_locn e
  | [] -> Ast.Unknown
let inhabited_census_lookup (p : Path.t) : (string * inh_status) option =
  Option.map snd
    (List.find_opt (fun (q, _) -> Path.compare p q = 0) !St.inhabited_census)
(* LEM_INH_DEBUG set: trace the Inhabited census on stderr (DESIGN,
   "Debugging the analyses"). *)
let inhabited_census_debug = Sys.getenv_opt "LEM_INH_DEBUG" <> None
let inhabited_census_add (p : Path.t) (name : string) (st : inh_status) : unit =
  St.inhabited_census := (p, (name, st)) :: !St.inhabited_census;
  if inhabited_census_debug then
    Printf.eprintf "CENSUS add %s (%s) %s\n%!" (Path.to_string p) name
      (match st with Inh_none -> "NONE" | Inh_instances es -> String.concat ";" (List.map (fun e -> Printf.sprintf "[%s]" (String.concat "," (List.map string_of_int e))) es))
(* Known bounded Inhabited instances for library/target types the census
   cannot see (their lem types carry target_reps, so the backend emits no
   instances for them). Positions index the type's arguments:
   - either -> Lean Sum: LemLib's bounded inl/inr pair
     (lean-lib/LemLib.lean:90-91) — left side first (default priority).
   - vector: inhabitation needs an element to replicate.
   Every other head defaults to [[]]: assume an unconditional instance
   exists. This is the same assumption the tier-1 machinery has always
   made when emitting `default` at an applied type; if it is wrong, Lean
   reports a loud 'failed to synthesize' error at the emitted instance —
   visible, never a hidden inconsistency. *)
let lean_builtin_inhabited_entries (p : Path.t) : int list list =
  match Name.to_string (Path.get_name p) with
    | "either" -> [[0]; [1]]
    | "vector" -> [[0]]
    | _ -> [[]]
let inhabited_plan_lookup (p : Path.t) : inh_plan option =
  Option.map snd
    (List.find_opt (fun (q, _) -> Path.compare p q = 0) !St.inhabited_tier2_plans)
let inhabited_plan_add (p : Path.t) (pl : inh_plan) : unit =
  St.inhabited_tier2_plans := (p, pl) :: !St.inhabited_tier2_plans

let lean_reader_is_reader env cref =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  Targetset.mem Target_lean cd.reader

let lean_reader_is_seed env cref =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  Targetset.mem Target_lean cd.reader_seed

let lean_reader_param_name env cref =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  String.concat "" ["_lemReader_"; Name.to_string (Path.get_name cd.const_binding)]

(* reader_consumer (declare {lean} reader_consumer val f):
   a target_rep'd val declared a READER CONSUMER — its generated call
   sites pass ALL reader parameters as extra leading arguments (global
   sorted order, before f's own arguments), its callers get lifted by
   the ordinary reader fixpoint, and the hand-written implementation
   declares the matching leading parameters explicitly. Injection is
   routed through reader_inject_name, so inside a reader_seed def the
   seed's first argument is passed instead of the binder — no new seed
   machinery. *)
let lean_reader_is_consumer env cref =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  Targetset.mem Target_lean cd.reader_consumer

(* `declare {lean} effectful val` is refused on the Lean target. The
   mechanism it named — call-site wraps crossing from a `BaseIO`
   representation back into pure types through a library axiom — was
   removed because that crossing was an unprovable trust boundary in every
   downstream proof cone (DESIGN, "Zero axioms; effects as explicit
   state"; the deletion record is
   doc/lean-backend/2026-09-01_L2-deletion-record.md). The annotation
   itself (grammar word, `Decl_effectful`, the `const_descr.effectful`
   field) is retained for other targets' potential use; its Lean-target
   handling is this fail-closed refusal. Fires for every
   {lean}-effectful-marked constant even if unused; idempotent; run at
   every pre-pass entry. *)
let lean_effectful_retired_check env =
  List.iter (fun cref ->
      let cd = c_env_lookup Ast.Unknown env.c_env cref in
      if Targetset.mem Target_lean cd.effectful then
        raise (Reporting_basic.err_general true cd.spec_l
          (Printf.sprintf
            "Lean backend: val %s — 'declare {lean} effectful' is retired on the lean target; use supply lifting instead ('declare {lean} supply val', the deterministic state-passing transform): an effectful target representation crossed from BaseIO back into pure types through a library axiom, which is gone (doc/lean-backend/DESIGN.md, \"Zero axioms; effects as explicit state\")"
            (Name.to_string (Path.get_name cd.const_binding)))))
    (c_env_all_consts env.c_env)

(* Guards RC-rep / RC-mix, fail-closed for every consumer-marked
   constant even if unused: the consumer IS an extern boundary, so it
   must carry an identifier-form Lean target_rep (a parameter-binding
   rep would consume the leading reader arguments positionally; an
   infix or missing rep has no sound leading-argument position), and
   it cannot simultaneously be a reader / reader_seed / supply val.
   Idempotent; run at every pre-pass entry. *)
let lean_reader_consumer_check env =
  List.iter (fun cref ->
      if lean_reader_is_consumer env cref then begin
        let cd = c_env_lookup Ast.Unknown env.c_env cref in
        let cname = Name.to_string (Path.get_name cd.const_binding) in
        let mix which =
          raise (Reporting_basic.err_general true cd.spec_l
            (Printf.sprintf
              "Lean backend: val %s is declared both {lean} reader_consumer and {lean} %s (unsupported: RC-mix — one mechanism per val)"
              cname which)) in
        if Targetset.mem Target_lean cd.reader then mix "reader";
        if Targetset.mem Target_lean cd.reader_seed then mix "reader_seed";
        if Targetset.mem Target_lean cd.supply then mix "supply";
        (match Target.Targetmap.apply_target cd.target_rep
                 (Target.Target_no_ident Target.Target_lean) with
         | Some (CR_simple (_, _, [], _)) | Some (CR_inline (_, _, [], _)) -> ()
         | Some (CR_simple _) | Some (CR_inline _) ->
           raise (Reporting_basic.err_general true cd.spec_l
             (Printf.sprintf
               "Lean backend: reader_consumer val %s has a parameter-binding Lean target_rep (unsupported: RC-rep — the reader arguments are passed as leading POSITIONAL arguments, which a substituting rep would consume; use an identifier-form rep whose implementation takes the reader parameters explicitly)"
               cname))
         | Some _ ->
           raise (Reporting_basic.err_general true cd.spec_l
             (Printf.sprintf
               "Lean backend: reader_consumer val %s has an unsupported Lean target_rep form (RC-rep: identifier-form reps only)"
               cname))
         | None ->
           raise (Reporting_basic.err_general true cd.spec_l
             (Printf.sprintf
               "Lean backend: reader_consumer val %s has no Lean target_rep (RC-rep: the consumer is an extern boundary by definition — give it an identifier-form rep whose implementation takes the reader parameters as leading arguments)"
               cname)))
      end)
    (c_env_all_consts env.c_env)

(* Binder names key on the constant's UNQUALIFIED name: two reader (or
   supply) constants with the same name in different modules would emit
   the same binder and silently conflate — fail closed,
   naming both. *)
let lean_param_dup_check env (mechanism : string) (l : (Types.const_descr_ref * string) list) =
  let rec go = function
    | (c1, n1) :: (((c2, n2) :: _) as rest) ->
      if n1 = n2 then begin
        let path c =
          Path.to_string ((c_env_lookup Ast.Unknown env.c_env c).const_binding) in
        raise (Reporting_basic.err_general true Ast.Unknown
          (Printf.sprintf
            "Lean backend: two %s constants share the unqualified name behind binder '%s' (%s and %s) — their injected binders would silently conflate; rename one of them"
            mechanism n1 (path c1) (path c2)))
      end else go rest
    | _ -> () in
  go l

let lean_reader_get_params env =
  match !St.reader_params_cache with
  | Some l -> l
  | None ->
    let l =
      List.filter_map (fun cref ->
          if lean_reader_is_reader env cref
          then Some (cref, lean_reader_param_name env cref)
          else None)
        (c_env_all_consts env.c_env) in
    let l = List.sort (fun (_, a) (_, b) -> String.compare a b) l in
    lean_param_dup_check env "reader" l;
    St.reader_params_cache := Some l; l

(* Pre-pass over one module's defs: grow St.reader_lifted to a fixpoint —
   a def is lifted if it (transitively) uses a reader constant or a lifted
   def. Must run BEFORE emission (defs renders last-to-first). The set
   persists across modules (processed in dependency order). Instance defs
   are never lifted (their methods cannot take extra parameters); an
   instance method that uses a lifted/reader constant fails closed at
   emission. Nested modules collect at Val_def granularity. *)
(* ===== Fuel lifting =====

   Classic mechanism name: an instance-implicit READER of the ambient
   fuel. `declare {lean} fuel val f = `sentinel`` makes `f` a total
   worker recursing structurally on its own fuel counter (`lemFuel`);
   the counter STARTS at the ambient fuel, which is a parameter of the
   generated code — never a numeral ([USER 2026-09-03], "No magic
   values", doc/lean-backend/DESIGN.md). The ambient is the LemLib class
   `LemFuel` (one field, `fuel : Nat`): every def that (transitively)
   reaches a fuel'd constant, a fuel-lifted def, or a
   `declare {lean} fuel_consumer val` (a hand-written Lean implementation
   that reads `LemFuel.fuel`) takes an instance-implicit `[LemFuel]`
   binder; call sites are textually unchanged (Lean's instance
   resolution passes the binder along); the entry point instantiates it
   (`@f ⟨n⟩ …` / `letI : LemFuel := ⟨n⟩`), and a theorem quantifies over
   it. Fail-closed: a reference to a fuel-lifted constant where no
   `[LemFuel]` is in scope (instance method, indreln rule, lemma/assert)
   is a generation-time error (fuel_scope_check) — there is no default
   to fall back on, by design. *)

let lean_fuel_is_fuelled env cref =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  Target.Targetmap.apply_target cd.fuel_sentinel (Target.Target_no_ident Target.Target_lean) <> None

let lean_fuel_is_consumer env cref =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  Targetset.mem Target_lean cd.fuel_consumer

let lean_has_lean_rep env cref =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  Target.Targetmap.apply_target cd.target_rep (Target.Target_no_ident Target.Target_lean) <> None

(* ===== Fuel measures (declare {lean} fuel_measure val f = `expr`) =====

   Classic mechanism name: a DATA MEASURE instantiating the fuel — form
   (c) of DESIGN.md's "No magic values" for a fuel'd function. The
   ruling ([USER 2026-09-04]): the lem sources are NOT restructured for
   Lean's structural checker ("we maintain the lem structure, and we get
   additional properties we want without any trust decrease"); the fuel
   worker stays exactly as generated (the OCaml output is untouched by
   construction), and the WRAPPER of a measured function instantiates the
   worker's counter from a Lean expression over the function's own
   parameters instead of the ambient `[LemFuel]`:

       def f (x : T) : R := f_lemFuel (<measure>) x

   so `f` is fuel-FREE for its callers (no `[LemFuel]` binder unless its
   body passes the ambient on to another fuel'd function; the fuel
   fixpoint treats a measured constant as a non-fuel'd one). The
   companion obligation — the measure is a SUFFICIENT fuel — is emitted
   as a theorem STATEMENT in the module's auxiliary file,

       theorem f_measure_sufficient (x : T) (lemFuel : Nat)
           (lemMeasureLe : <measure> ≤ lemFuel) :
           f_lemFuel lemFuel x = f x := <Module>_lemMeasureProofs.f_measure_sufficient x lemFuel lemMeasureLe

   whose proof the consumer supplies in the hand-written module
   `<Module>_lemMeasureProofs` (imported by the auxiliary file): the Lean
   build FAILS without it — no measured function ships without its
   theorem.

   The HYPOTHESIS-CARRYING form ([USER 2026-09-05] "agree, go ahead with
   option 1"; doc/lean-backend/2026-09-05_measure-hypothesis-record.md):
   ``fuel_measure val f = `<measure>` assuming
   `<H>` `` where H is a Lean Prop over the same parameters. The WRAPPER
   is unchanged (fuel-free: `def f x := f_lemFuel (<measure>) x`); the
   obligation gains H as the binder named `lemHyp`, placed immediately
   BEFORE `lemFuel`:

       theorem f_measure_sufficient (x : T) (lemHyp : (<H>)) (lemFuel : Nat)
           (lemMeasureLe : (<measure>) ≤ lemFuel) :
           f_lemFuel lemFuel x = f x := <Module>_lemMeasureProofs.f_measure_sufficient x lemHyp lemFuel lemMeasureLe

   i.e. `H xs → μ xs ≤ fuel → f_lemFuel fuel xs = f xs`. Operationally:
   on inputs violating H the wrapper may exhaust (the sentinel — loud by
   convention), which is admissible because the oracle's own behaviour
   on those inputs is not the semantics anyone relies on (a tag
   environment the frontend never produces; a basis below 2 the callers
   never pass); the consumer's theorems carry H exactly as they already
   assume well-formedness. A consumer-side gate tells the two forms apart
   deterministically: the conditional form has a binder NAMED `lemHyp`
   (Prop-typed, mentioning only the parameters) immediately before the
   `lemFuel : Nat` binder; the unconditional form has no binder of that
   name (`lemHyp` is a reserved synthesized name). Refusals on H
   (lean_render_param_expr, the measure's rules under the hypothesis
   reading): FH-vacuous (a hypothesis mentioning no parameter — `True`, a
   closed term: the unconditional form in disguise, refused to keep the
   two forms distinct), FH-free, FH-ambient (`LemFuel`: the hypothesis
   may not mention the fuel), the reserved `lemFuel`/`lemMeasureLe`/
   `lemHyp`/`_lem…` binders, FH-root, FH-sizeOf (one vocabulary for
   measure and hypothesis). Whether H is a Prop is Lean's check at build
   time (`(lemHyp : (H))` fails to elaborate otherwise). Fail-closed rules (lean_fuel_measure_check + the emission
   guards): FM-nofuel (a measure needs the fuel worker), FM-consumer,
   FM-structural (one shape per definition), FM-free (an unqualified
   identifier in the measure that is not a parameter — a global Lean name
   must be qualified; every dotted COMPONENT of every identifier is tested
   against the forbidden names and `_root_` is refused: FM-root), FM-sizeOf (Lean's automatic `SizeOf` instances are
   noncomputable — measured: `List._sizeOf_inst … has no
   executable code`; a measure must execute), FM-ambient
   (`LemFuel` in a measure), FM-literal / FM-const (a numeral, or any
   measure mentioning no parameter: not a DATA measure — a magic value),
   FM-mutual (all-or-none in a truly mutual fuel'd block), FM-supply
   (unsupported combination), FM-library (a library module's auxiliary
   file is not built, so its obligation would have no home). *)

let lean_fuel_measure_for env cref =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  Target.Targetmap.apply_target cd.fuel_measure (Target.Target_no_ident Target.Target_lean)

let lean_fuel_is_measured env cref = lean_fuel_measure_for env cref <> None

(* A fuel'd constant whose wrapper reads the AMBIENT fuel — the one kind
   that makes its callers fuel-lifted. A measured constant is fuel'd (it
   has a worker) but not ambient. *)
let lean_fuel_is_ambient env cref =
  lean_fuel_is_fuelled env cref && not (lean_fuel_is_measured env cref)

(* Guards FM-consumer / FM-structural / FM-nofuel, fail-closed for every
   marked constant even if unused; idempotent; run FIRST at every pre-pass
   entry (so a measure conflict is reported as such, before the FC/ST
   checks would report the same val for another reason). *)
let lean_fuel_measure_check env =
  List.iter (fun cref ->
      let cd = c_env_lookup Ast.Unknown env.c_env cref in
      if lean_fuel_is_measured env cref then begin
        let cname = Name.to_string (Path.get_name cd.const_binding) in
        if Targetset.mem Target_lean cd.fuel_consumer then
          raise (Reporting_basic.err_general true cd.spec_l
            (Printf.sprintf
              "Lean backend: val %s carries both 'declare {lean} fuel_consumer val' and 'declare {lean} fuel_measure val' (FM-consumer: a fuel_consumer is a hand-written implementation that reads the ambient fuel; a measure instantiates a GENERATED worker's counter — the two exclude each other)"
              cname));
        if Targetset.mem Target_lean cd.structural then
          raise (Reporting_basic.err_general true cd.spec_l
            (Printf.sprintf
              "Lean backend: val %s carries both 'declare {lean} structural val' and 'declare {lean} fuel_measure val' (FM-structural: a structural def has no fuel counter to instantiate — declare exactly one shape)"
              cname));
        if not (lean_fuel_is_fuelled env cref) then
          raise (Reporting_basic.err_general true cd.spec_l
            (Printf.sprintf
              "Lean backend: 'declare {lean} fuel_measure val %s' without a 'declare {lean} fuel val %s = `sentinel`' on the same val (FM-nofuel: the measure instantiates the fuel WORKER's counter, so the worker must exist)"
              cname cname))
      end)
    (c_env_all_consts env.c_env)

(* The measure is a Lean expression over the function's parameters. Its
   identifier tokens are classified (fail-closed): a parameter (by its
   lem name; substituted by the rendered Lean binder — dotted projections
   `x.1`/`x.length` allowed), a QUALIFIED global (`Ns.f` —
   Lean's global namespace is not visible at generation, so a global must
   be spelled with its namespace, which also keeps it from shadowing a
   parameter), or refused: `LemFuel…` (FM-ambient: a measure that reads
   the ambient is not a data measure), the reserved `lemFuel`/`_lem…`
   binders, `sizeOf`/`SizeOf.…` (FM-sizeOf: noncomputable, cannot be the
   wrapper's runtime counter), and any other unqualified name (FM-free —
   Lean keywords such as `fun`/`if` included: a measure is a plain
   expression). A measure
   mentioning NO parameter is refused (FM-literal for a bare numeral,
   FM-const otherwise): nothing about the data bounds it — the magic
   value itself. Tokens: ASCII letters/`_` and Lean's LETTER-LIKE Unicode
   code points (Greek but λ/Π/Σ, Coptic, the letterlike block ℕ…, script/
   double-struck/fraktur letters, subscripts — Lean's `isLetterLike`/
   `isSubScriptAlnum`) start an identifier, continued by those plus
   digits, `'`, `.`, `!`, `?`; digits start a numeral; everything else —
   ASCII punctuation and every OTHER Unicode code point (`≤`, `∧`, `∀`,
   `→`, `≠`, `∈`, `¬`, `×`: the operators a Prop is written with) —
   passes through unchanged. (Before the hypothesis form existed every
   non-ASCII byte was an identifier character, which made `2 ≤ b` the
   free variable `≤`; a measure had no need of Unicode operators.) *)
type lean_measure_token = LM_ident of string | LM_num of string | LM_other of string

(* UTF-8: the code point at byte i and the byte length of its encoding
   (a malformed lead byte is treated as a one-byte non-letter symbol, so
   it passes through and Lean reports it). *)
let lean_utf8_decode (m : string) (i : int) : int * int =
  let n = String.length m in
  let b k = if i + k < n then Char.code m.[i + k] else 0 in
  let c0 = b 0 in
  if c0 < 0x80 then (c0, 1)
  else if c0 land 0xE0 = 0xC0 && i + 1 < n then (((c0 land 0x1F) lsl 6) lor (b 1 land 0x3F), 2)
  else if c0 land 0xF0 = 0xE0 && i + 2 < n then
    (((c0 land 0x0F) lsl 12) lor ((b 1 land 0x3F) lsl 6) lor (b 2 land 0x3F), 3)
  else if c0 land 0xF8 = 0xF0 && i + 3 < n then
    (((c0 land 0x07) lsl 18) lor ((b 1 land 0x3F) lsl 12) lor ((b 2 land 0x3F) lsl 6) lor (b 3 land 0x3F), 4)
  else (c0, 1)

(* Lean's `isLetterLike` ∪ `isSubScriptAlnum` — `Init/Meta/Defs.lean`
   (4.28.0 :100–118, 4.32.2 :108–118, identical): Latin-1 supplement
   letters but × ÷, Latin Extended-A, Greek but λ/Π/Σ, Coptic, polytonic
   Greek, the letterlike block, script/double-struck/fraktur, the
   subscript ranges and U+2C7C (without the first two ranges and U+2C7C,
   `ñ` passed through as an operator). *)
let lean_is_letter_like (c : int) : bool =
  (0xc0 <= c && c <= 0xff && c <> 0xd7 && c <> 0xf7)          (* Latin-1 supplement letters but × ÷ *)
  || (0x100 <= c && c <= 0x17f)                               (* Latin Extended-A *)
  || (0x3b1 <= c && c <= 0x3c9 && c <> 0x3bb)                 (* lower Greek but λ *)
  || (0x391 <= c && c <= 0x3a9 && c <> 0x3a0 && c <> 0x3a3)   (* upper Greek but Π, Σ *)
  || (0x3ca <= c && c <= 0x3fb)                               (* Coptic *)
  || (0x1f00 <= c && c <= 0x1ffe)                             (* polytonic Greek *)
  || (0x2100 <= c && c <= 0x214f)                             (* letterlike block *)
  || (0x1d49c <= c && c <= 0x1d59f)                           (* script/double-struck/fraktur *)
  || (0x2080 <= c && c <= 0x2089) || (0x2090 <= c && c <= 0x209c) || (0x1d62 <= c && c <= 0x1d6a)  (* subscripts *)
  || c = 0x2c7c                                               (* ⱼ, isSubScriptAlnum *)

let lean_measure_tokens (m : string) : lean_measure_token list =
  let n = String.length m in
  (* classify the code point at i: `Start (len) | `Cont (len) | `Digit | `Other (len) *)
  let classify i =
    let c = m.[i] in
    if Char.code c < 128 then begin
      if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_' then (`Alpha, 1)
      else if c >= '0' && c <= '9' then (`Digit, 1)
      else if c = '\'' || c = '.' || c = '!' || c = '?' then (`Cont, 1)
      else (`Other, 1)
    end else begin
      let (cp, len) = lean_utf8_decode m i in
      if lean_is_letter_like cp then (`Alpha, len) else (`Other, len)
    end in
  let rec go i acc =
    if i >= n then List.rev acc
    else begin
      match classify i with
      | (`Alpha, len) ->
        let j = ref (i + len) in
        let continue_ = ref true in
        while !continue_ && !j < n do
          (match classify !j with
           | ((`Alpha | `Digit | `Cont), l) -> j := !j + l
           | (`Other, _) -> continue_ := false)
        done;
        go !j (LM_ident (String.sub m i (!j - i)) :: acc)
      | (`Digit, _) ->
        let j = ref (i + 1) in
        while !j < n && m.[!j] >= '0' && m.[!j] <= '9' do incr j done;
        go !j (LM_num (String.sub m i (!j - i)) :: acc)
      | ((`Cont | `Other), len) ->
        go (i + len) (LM_other (String.sub m i len) :: acc)
    end in
  go 0 []

(* Derived-size census lookup (mechanism comment at lean_size_shape,
   below). *)
let size_census_lookup (p : Path.t) : size_status option =
  Option.map snd (List.find_opt (fun (q, _) -> Path.compare p q = 0) !St.size_census)

(* What is being rendered over the parameters: the measure (a Nat the
   wrapper executes) or the `assuming` hypothesis (a Prop the obligation
   binds as `lemHyp`). Same tokenizer, same scope rules, same forbidden
   names; the tags in the messages and the parameter-free refusal differ
   (FM-literal/FM-const vs FH-vacuous). *)
type lean_param_expr_kind = LPE_measure | LPE_hypothesis

let lean_render_param_expr (kind : lean_param_expr_kind) (d : Types.type_defs) (l : Ast.l) (fname : string)
    (params : (string * (string * Types.t)) list) (measure : string) : string =
  let toks = lean_measure_tokens measure in
  let param_names = String.concat ", " (List.map fst params) in
  let what = match kind with LPE_measure -> "fuel measure" | LPE_hypothesis -> "measure hypothesis (`assuming`)" in
  let tag pre = String.concat "" [(match kind with LPE_measure -> "FM-" | LPE_hypothesis -> "FH-"); pre] in
  let mentions = ref 0 in
  let starts_with pre s =
    String.length s >= String.length pre && String.sub s 0 (String.length pre) = pre in
  (* `lemSize x` (mechanism comment at lean_size_shape):
     the derived size of the parameter x's type — resolved through the
     size census to `<Type>.lemSize x`; refused when x is not a parameter
     (FM-size-param) or its type has no derived size (FM-size-type, with
     the census's reason). *)
  let render_lem_size (rest : lean_measure_token list) : string * lean_measure_token list =
    let rec skip_ws acc = function
      | LM_other s :: tl when List.mem s [" "; "\t"; "\n"] -> skip_ws (String.concat "" [acc; s]) tl
      | tl -> (acc, tl) in
    let (ws_, tl) = skip_ws "" rest in
    match tl with
      | LM_ident x :: tl' when not (String.contains x '.') && List.mem_assoc x params ->
        let (bind, ty) = List.assoc x params in
        incr mentions;
        let ty' = Types.head_norm d ty in
        (match ty'.Types.t with
          | Types.Tapp (_, p) ->
            (match size_census_lookup p with
              | Some (Size_fn tname) -> (String.concat "" [tname; ".lemSize"; ws_; bind], tl')
              | Some (Size_none reason) ->
                raise (Reporting_basic.err_general true l
                  (Printf.sprintf
                    "Lean backend: the %s of %s uses `lemSize %s`, but the type of %s (%s) has no derived size function (FM-size-type: it is %s); a size is derived for every recursive block of generated inductive types in a user module (`t.lemSize`)"
                    what fname x x (Path.to_string p) reason))
              | None ->
                raise (Reporting_basic.err_general true l
                  (Printf.sprintf
                    "Lean backend: the %s of %s uses `lemSize %s`, but the type of %s (%s) is not a generated inductive type of this invocation (FM-size-type: no derived size function exists for it — a size is derived for every recursive block of generated inductive types in a user module)"
                    what fname x x (Path.to_string p))))
          | _ ->
            raise (Reporting_basic.err_general true l
              (Printf.sprintf
                "Lean backend: the %s of %s uses `lemSize %s`, but %s is not of a generated inductive type (FM-size-type: `lemSize` is the backend-derived structural size, defined for the recursive blocks of generated inductives; for a list use `List.length %s`, for a nat the parameter itself)"
                what fname x x x)))
      | _ ->
        let usable = List.filter (fun (n, _) -> n <> "lemSize") params in
        let usable_names = String.concat ", " (List.map fst usable) in
        raise (Reporting_basic.err_general true l
          (Printf.sprintf
            "Lean backend: `lemSize` in the %s of %s must be applied directly to one of the parameters %s (FM-size-param: `lemSize x` — the backend resolves x's type to its derived size function `t.lemSize`; any other argument shape is refused%s)"
            what fname (if usable = [] then "(none)" else usable_names)
            (if List.mem_assoc "lemSize" params
             then "; `lemSize` is a reserved word inside a measure, so the PARAMETER named `lemSize` cannot be mentioned there — rename it"
             else "")))
  in
  let rec render acc = function
    | [] -> acc
    | (LM_other s | LM_num s) :: tl -> render (String.concat "" [acc; s]) tl
    | LM_ident t :: tl ->
      let head, rest =
        match String.index_opt t '.' with
        | Some i -> String.sub t 0 i, String.sub t i (String.length t - i)
        | None -> t, "" in
      (* the forbidden names are tested on EVERY dotted component, not the
         head only, and `_root_` is refused outright:
         `_root_.LemFuel.fuel + 0 * List.length l` and `_root_.sizeOf l`
         passed the head-only checks (the first compiled to a
         fuel-DEPENDENT wrapper whose obligation is false; the second was
         caught only by Lean). A qualified global never needs `_root_`. *)
      let components = String.split_on_char '.' t in
      (* `True` is the unconditional form in disguise and `False` makes the
         obligation say nothing: both vacuous (checked before FH-free, which
         would otherwise report them as unqualified names) *)
      if kind = LPE_hypothesis && (t = "True" || t = "False") then
        raise (Reporting_basic.err_general true l
          (Printf.sprintf
            "Lean backend: the measure hypothesis of %s is `%s` (FH-vacuous: `True` is the unconditional form — write the measure without `assuming`; `False` would make the obligation say nothing)"
            fname t))
      else if head = "_root_" then
        raise (Reporting_basic.err_general true l
          (Printf.sprintf
            "Lean backend: the %s of %s mentions `%s` (%s: a `_root_`-qualified name is refused — a qualified global never needs it, and it would bypass the checks on the name's components)"
            what fname t (tag "root")))
      else if List.exists (fun c -> c = "sizeOf" || c = "SizeOf") components then
        raise (Reporting_basic.err_general true l
          (Printf.sprintf
            "Lean backend: the %s of %s uses `%s` (%s: Lean's automatic `SizeOf` instances are NONCOMPUTABLE — the wrapper must execute, so a measure is a computable expression: `List.length xs + 1`, `n + 1`, the backend-derived structural size `lemSize x` of a parameter of a generated inductive type, or a hand-written structural size function `Ns.size x` in a Lean module the generated module imports via `declare {lean} extra_import`; a hypothesis is stated in the same vocabulary)"
            what fname t (tag "sizeOf")))
      else if List.exists (fun c -> c = "LemFuel") components then
        raise (Reporting_basic.err_general true l
          (Printf.sprintf
            "Lean backend: the %s of %s mentions `%s` (%s: a measure that reads the ambient fuel is not a data measure, and a hypothesis may not mention the fuel — it must be an expression over the parameters %s)"
            what fname t (tag "ambient") param_names))
      else if List.exists (fun c -> c = "lemFuel" || c = "lemMeasureLe" || c = "lemHyp" || starts_with "_lem" c) components then
        raise (Reporting_basic.err_general true l
          (Printf.sprintf
            "Lean backend: the %s of %s mentions the reserved binder `%s` (the backend's synthesized names `lemFuel`, `lemMeasureLe`, `lemHyp`, `_lem…` are not the function's parameters; a hypothesis in particular may not mention the fuel)"
            what fname t))
      else if t = "lemSize" then begin
        let (out, tl') = render_lem_size tl in
        render (String.concat "" [acc; out]) tl'
      end
      else if List.mem_assoc head params then begin
        incr mentions; render (String.concat "" [acc; fst (List.assoc head params); rest]) tl
      end
      else if rest <> ""
              && List.exists (fun c -> c <> "" && String.for_all (fun ch -> ch >= '0' && ch <= '9') c)
                   (List.tl components) then
        (* `env.1` where `env` is not a parameter: a numeral component is a
           PROJECTION, never a namespace, so the head had to be a parameter
           (found on the cerberus dry run: lem's rename pass had made the
           parameter `env1`, and `env.1` passed as a qualified global) *)
        raise (Reporting_basic.err_general true l
          (Printf.sprintf
            "Lean backend: `%s` in the %s of %s is a projection on `%s`, which is not a parameter (%s: the parameters are %s — note that lem's rename pass may have renamed a clashing variable, e.g. `env` to `env1`; a qualified global has no numeral component)"
            t what fname head (tag "free") (if params = [] then "none" else param_names)))
      else if rest <> "" then render (String.concat "" [acc; t]) tl
      else
        raise (Reporting_basic.err_general true l
          (Printf.sprintf
            "Lean backend: free variable `%s` in the %s of %s (%s: a measure or hypothesis mentions only the function's parameters — here %s — and QUALIFIED Lean names such as `List.length xs`, `Ns.size x` or `Ns.WellFormed env`, or `lemSize x` for the derived size of a parameter's inductive type; Lean's global namespace is not visible at generation, so an unqualified name that is not a parameter is refused)"
            t what fname (tag "free") (if params = [] then "none" else param_names)))
  in
  let rendered = render "" toks in
  if !mentions = 0 then begin
    let significant = List.filter (function
        | LM_other s -> not (List.mem s [" "; "\t"; "\n"; "("; ")"])
        | _ -> true) toks in
    match kind, significant with
    | LPE_hypothesis, _ ->
      (* a parameter-free hypothesis (`True`, a closed proposition) is the
         unconditional obligation in disguise: refused so that the two
         forms stay distinct (a consumer gate reads the `lemHyp` binder as
         "conditional") *)
      raise (Reporting_basic.err_general true l
        (Printf.sprintf
          "Lean backend: the measure hypothesis of %s (`%s`) mentions none of its parameters %s (FH-vacuous: a hypothesis qualifies the obligation by a fact about the ARGUMENTS — `2 ≤ b`, `Ns.Acyclic env`; a closed proposition such as `True` is the unconditional form, so write the measure without `assuming`)"
          fname (String.trim measure) (if params = [] then "(none)" else param_names)))
    | LPE_measure, [LM_num _] ->
      raise (Reporting_basic.err_general true l
        (Printf.sprintf
          "Lean backend: the %s of %s is the numeral `%s` (FM-literal: a literal fuel is a magic value, forbidden by design — doc/lean-backend/DESIGN.md, \"No magic values\"; a fuel measure is an expression over the parameters %s, e.g. `List.length xs + 1`)"
          what fname (String.trim measure) (if params = [] then "(none)" else param_names)))
    | LPE_measure, _ ->
      raise (Reporting_basic.err_general true l
        (Printf.sprintf
          "Lean backend: the %s of %s (`%s`) mentions none of its parameters %s (FM-const: a DATA measure is a function of the data; a constant measure is a magic value)"
          what fname (String.trim measure) (if params = [] then "(none)" else param_names)))
  end;
  rendered

let lean_render_measure d l fname params measure =
  lean_render_param_expr LPE_measure d l fname params measure
let lean_render_hypothesis d l fname params hyp =
  lean_render_param_expr LPE_hypothesis d l fname params hyp

(* Guards FC-rep / FC-inert, fail-closed for every marked constant even if
   unused; idempotent; run at every pre-pass entry.
   - FC-rep: a fuel_consumer IS a hand-written extern boundary, so it
     must carry a Lean target_rep (a generated definition's fuel needs
     are computed by the lifting itself; the declare would be
     meaningless on it).
   - FC-inert: a fuel SENTINEL on a target_rep'd val is silently inert
     (its lem definition renders as a comment, no worker/wrapper is ever
     emitted) — if the hand-written implementation takes the fuel,
     declare it a fuel_consumer instead. *)
let lean_fuel_consumer_check env =
  List.iter (fun cref ->
      let cd = c_env_lookup Ast.Unknown env.c_env cref in
      let cname = Name.to_string (Path.get_name cd.const_binding) in
      if lean_fuel_is_consumer env cref && not (lean_has_lean_rep env cref) then
        raise (Reporting_basic.err_general true cd.spec_l
          (Printf.sprintf
            "Lean backend: val %s is declared {lean} fuel_consumer but has no Lean target_rep (FC-rep: the declare marks a hand-written implementation that reads LemFuel.fuel; a generated definition's fuel needs are computed by the fuel lifting — drop the declare)"
            cname));
      if lean_fuel_is_fuelled env cref && lean_has_lean_rep env cref then
        raise (Reporting_basic.err_general true cd.spec_l
          (Printf.sprintf
            "Lean backend: 'declare {lean} fuel val %s' on a val that carries a Lean target_rep (FC-inert: its lem definition renders as a comment and no fuel worker is emitted, so the declare is silently inert; if the hand-written implementation reads the ambient fuel, declare it '{lean} fuel_consumer' instead)"
            cname)))
    (c_env_all_consts env.c_env)

(* ===== Structural recursion (declare {lean} structural val) =====

   Classic mechanism name: STRUCTURAL RECURSION, checked by Lean's own
   termination checker — the admissible form (c) of DESIGN.md's "No magic
   values" (nothing chosen, no bound, a proof unfolds it). A recursive lem
   definition marked `declare {lean} structural val f` is emitted as an
   ORDINARY `def` (no `partial`, no fuel worker, no `[LemFuel]`) with an
   explicit `termination_by structural <param>` clause, so Lean must
   prove termination by structural recursion on the named parameter and
   may NOT fall back to well-founded recursion (form (b): admissible, but
   the kernel cannot compute through it — the consumer's `join` finding).
   The parameter is chosen by lean_structural_assign (below): the syntactic
   analysis that Lean's checker also performs — at every self/sibling call
   the designated argument must be a variable bound by a constructor
   pattern (transitively) on the designated parameter. Where the analysis
   finds no such parameter, generation refuses with the lem location and
   the offending call; where it finds one and Lean's checker still
   disagrees, the Lean BUILD fails (`failed to infer structural
   recursion` / `Cannot use parameter …`) — that is the fail-closed
   backstop, exactly as for `fuel_consumer`. Contrast
   `declare {lean} termination_argument f = automatic` (lem's upstream
   vocabulary, honoured by this backend as a plain `def` with NO clause):
   Lean tries structural recursion and then well-founded recursion — a
   `def` either way, but kernel computability is not promised. *)

let lean_is_structural env cref =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  Targetset.mem Target_lean cd.structural

(* Guards ST-fuel / ST-inert / ST-term, fail-closed for every marked
   constant even if unused; idempotent; run at every pre-pass entry.
   - ST-fuel: fuel and structural are the two admissible shapes of a
     recursion ((B) and (A)); one definition carries one of them.
   - ST-inert: a target_rep'd val renders as a comment — the declare
     would be silently inert (the FC-inert rule).
   - ST-term: `termination_argument` already decides the keyword for the
     Lean target; two termination declares on one val contradict
     (`automatic` permits the well-founded fallback that `structural`
     forbids). *)
let lean_structural_check env =
  List.iter (fun cref ->
      let cd = c_env_lookup Ast.Unknown env.c_env cref in
      if Targetset.mem Target_lean cd.structural then begin
        let cname = Name.to_string (Path.get_name cd.const_binding) in
        if lean_fuel_is_fuelled env cref then
          raise (Reporting_basic.err_general true cd.spec_l
            (Printf.sprintf
              "Lean backend: val %s carries both 'declare {lean} fuel val' and 'declare {lean} structural val' (ST-fuel: a recursion is emitted either as a fuel worker or as a structural def — declare exactly one)"
              cname));
        if lean_has_lean_rep env cref then
          raise (Reporting_basic.err_general true cd.spec_l
            (Printf.sprintf
              "Lean backend: 'declare {lean} structural val %s' on a val that carries a Lean target_rep (ST-inert: its lem definition renders as a comment, so the declare is silently inert — drop it)"
              cname));
        (match Target.Targetmap.apply_target cd.termination_setting
                 (Target.Target_no_ident Target.Target_lean) with
         | Some _ ->
           raise (Reporting_basic.err_general true cd.spec_l
             (Printf.sprintf
               "Lean backend: val %s carries both 'declare termination_argument' and 'declare {lean} structural val' (ST-term: 'automatic' lets Lean fall back to well-founded recursion, which 'structural' forbids — declare exactly one)"
               cname))
         | None -> ())
      end)
    (c_env_all_consts env.c_env)

(* Pre-pass over one module's defs: grow St.fuel_lifted to a fixpoint — a
   def is fuel-lifted if it defines a fuel'd constant, or (transitively)
   uses a fuel'd constant, a fuel_consumer, or a fuel-lifted def. Val_def
   granularity, nested modules recursed, instances skipped (fail-closed
   at emission), the reader_prepass shape. Unlike the reader pre-pass,
   reader_seed defs ARE liftable (the fuel binder is orthogonal to the
   seed), and target_rep'd defs are NOT (their bodies are dead text; a
   hand-written rep that needs the fuel says so with fuel_consumer). *)
let lean_fuel_prepass env (ds : def list) =
  lean_fuel_measure_check env;
  lean_fuel_consumer_check env;
  lean_structural_check env;
  let target = Target.Target_no_ident Target.Target_lean in
  let rec def_infos acc (((d_aux, _), _, _) as d : def) =
    match d_aux with
    | Instance _ -> acc
    | Module (_, _, _, _, _, inner_ds, _) -> List.fold_left def_infos acc inner_ds
    | Val_def _ ->
      let defined = (add_def_entities target true empty_used_entities d).used_consts_set in
      if Types.Cdset.exists (lean_has_lean_rep env) defined then acc
      else
        let used = (add_def_entities target false empty_used_entities d).used_consts_set in
        (defined, used) :: acc
    (* An inductive relation whose premises
       reach the ambient fuel takes `[LemFuel]` as an inductive PARAMETER
       (Lean allows an instance-implicit binder on an inductive; the
       constructors' premises then resolve the ambient from it) — so the
       relation is fuel-lifted like a def: a definition that mentions it
       takes the binder, and a reference from a fuel-free context (an
       assert, a lemma, an instance method) is the fuel_scope_check error.
       All relations of one indreln block lift together (one def). *)
    | Indreln _ ->
      let defined = (add_def_entities target true empty_used_entities d).used_consts_set in
      let used = (add_def_entities target false empty_used_entities d).used_consts_set in
      (defined, used) :: acc
    | _ -> acc in
  let infos = List.rev (List.fold_left def_infos [] ds) in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun (defined, used) ->
        if not (Types.Cdset.subset defined !St.fuel_lifted) then begin
          (* a MEASURED fuel'd constant is fuel-free for its callers (its
             wrapper's counter comes from the data): it is lifted only if
             its body reaches the ambient like any other def *)
          let needs =
            Types.Cdset.exists (lean_fuel_is_ambient env) defined
            || Types.Cdset.exists (fun c ->
                   lean_fuel_is_ambient env c || lean_fuel_is_consumer env c
                   || Types.Cdset.mem c !St.fuel_lifted)
                 used in
          if needs then begin
            St.fuel_lifted := Types.Cdset.union defined !St.fuel_lifted;
            changed := true
          end
        end) infos
  done

let lean_reader_prepass env (ds : def list) =
  lean_effectful_retired_check env;
  lean_reader_consumer_check env;
  if lean_reader_get_params env <> [] then begin
    let target = Target.Target_no_ident Target.Target_lean in
    (* Collect (defined, used) pairs at Val_def granularity, recursing into
       nested modules. Only Val_defs register their DEFINED constants:
       coarse add_def_entities on a whole Module def would also sweep class
       methods, val-spec-only constants, and indreln relation names into
       the lifted set, and caller-side
       injection would then poison their uses program-wide. Instances are
       skipped (fail-closed at emission); Class/Val_spec/Indreln/etc.
       cannot be lifted — a reader use inside an indreln rule or lemma is
       unsupported and fails visibly at the Lean build. *)
    let rec def_infos acc (((d_aux, _), _, _) as d : def) =
      match d_aux with
      | Instance _ -> acc
      | Module (_, _, _, _, _, inner_ds, _) -> List.fold_left def_infos acc inner_ds
      | Val_def _ ->
        let defined = (add_def_entities target true empty_used_entities d).used_consts_set in
        (* reader_seed defs are never lifted: they inject their own leading
           seed arguments (one per declared reader) internally, and their
           callers pass them explicitly. *)
        if Types.Cdset.exists (lean_reader_is_seed env) defined then acc
        else
          let used = (add_def_entities target false empty_used_entities d).used_consts_set in
          (defined, used) :: acc
      | _ -> acc in
    let infos = List.rev (List.fold_left def_infos [] ds) in
    let changed = ref true in
    while !changed do
      changed := false;
      List.iter (fun (defined, used) ->
          if not (Types.Cdset.subset defined !St.reader_lifted) then begin
            let needs =
              Types.Cdset.exists (fun c ->
                  lean_reader_is_reader env c || lean_reader_is_consumer env c)
                used
              || not (Types.Cdset.is_empty
                        (Types.Cdset.inter used !St.reader_lifted)) in
            if needs then begin
              St.reader_lifted := Types.Cdset.union defined !St.reader_lifted;
              changed := true
            end
          end) infos
    done
  end

(* ===== Instance-implicit readers
         (declare {lean} reader val r = instance `Cls.field`) =====

   Classic mechanism name: an IMPLICIT PARAMETER — the environment of a
   reader monad passed by type-class (instance) resolution, the shape of
   Haskell's implicit parameters (Lewis, Launchbury, Meijer, Shields,
   POPL 2000) and of Lean's own ambient-configuration classes. It is the
   reader lifting above with a different binder kind, and the fuel
   lifting with a user-named class:

   - `declare {lean} reader val r = instance `Cls.field`` makes the
     constant `r : unit -> T` an instance reader. The backticked text is
     the PROJECTION of a one-field Lean class (`class Cls where field :
     T`, hand-written by the consumer); the class is its namespace prefix
     (Lean names a structure's projections `Cls.field`). A read `r ()`
     emits `Cls.field` (a bare `r` emits `(fun (_ : Unit) => Cls.field)`).
   - Every definition that (transitively) reads `r`, calls a consumer of
     it, or calls such a definition binds `[Cls]` instance-implicitly —
     the same transitive fixpoint as the reader and fuel liftings
     (lean_ireader_prepass). Call sites are textually unchanged: Lean's
     instance resolution passes the binder along.
   - `declare {lean} reader_consumer val f = instance r` marks a
     hand-written target_rep'd `f` whose implementation reads `r`'s class
     itself (it declares `[Cls]` in its own signature): no argument is
     passed at its call sites; its callers bind `[Cls]`.
   - No instance exists in LemLib or in generated code (the fuel rule):
     the entry point supplies it (`@f ⟨v⟩ …`, `letI : Cls := ⟨v⟩`), and a
     theorem quantifies over it by binding `[Cls]`.
   - Binder position: immediately after `[LemFuel]` (wherever the fuel
     binder would stand), several instance readers in the GLOBAL order of
     lean_ireader_get_readers (sorted by the reader's lem name), BEFORE
     `[Inhabited tv]`, the fuel counter, the explicit reader binders and
     the supply binders.
   - Seeds: a `reader_seed` definition cuts EXPLICIT readers only; it is
     an ordinary member of this fixpoint, so an instance reader
     propagates THROUGH it (the seed def binds `[Cls]` itself). Instance
     readers are not seedable and are not counted among a seed's N
     positional seeds (N counts explicit readers only).
   - Mutual blocks: a mutual Val_def is one defined set, so its members
     are lifted all-or-none; fuel'd workers, wrappers, `_zero` lemmas and
     measure obligations all carry the binder.
   - Fail-closed: a read of an instance reader, or a reference to a
     member or consumer, where no `[Cls]` is in scope (instance methods,
     indreln rules, lemmas/asserts, target_rep'd bodies' contexts) is a
     generation-time error (ireader_scope_check) — there is no default
     to inject. Declaration errors (malformed projection, a polymorphic
     or non-`unit -> T` type, an inline Lean rep, a class shared by two
     readers up to its last component, a mix with another mechanism, a
     consumer naming a non-instance reader, a consumer without a Lean
     target_rep) are checked for every marked constant even if unused
     (lean_ireader_check); a reader with a lem body and no Lean
     target_rep is refused at its definition (IR-body, in the pre-pass).
   - No `.lem` using neither declaration form is affected: every path
     below is guarded by membership in these (empty) sets, and the
     declarations are `{lean}`-scoped, so no other target's output moves
     (record doc/lean-backend/2026-10-05_instance-reader-record.md). *)

let lean_ireader_projection env cref : string option =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  Target.Targetmap.apply_target cd.reader_instance (Target.Target_no_ident Target.Target_lean)

let lean_ireader_is_reader env cref = lean_ireader_projection env cref <> None

(* the instance readers a target_rep'd consumer's implementation reads *)
let lean_ireader_consumer_of env cref : Types.const_descr_ref list =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  match Target.Targetmap.apply_target cd.reader_consumer_instance
          (Target.Target_no_ident Target.Target_lean) with
  | Some l -> l
  | None -> []

(* `Cls.field` -> Some "Cls" when every dotted component is a plain Lean
   identifier and there are at least two; None otherwise (refused by
   lean_ireader_check: guillemets, spaces, `_root_` and single names have
   no unambiguous class prefix). *)
let lean_ireader_class_of_projection (proj : string) : string option =
  let comps = String.split_on_char '.' proj in
  let ident_ok c =
    String.length c > 0
    && c <> "_root_"
    && (match c.[0] with 'A'..'Z' | 'a'..'z' | '_' -> true | _ -> false)
    && String.for_all (fun ch -> match ch with
        | 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' | '\'' -> true | _ -> false) c in
  if List.length comps < 2 || not (List.for_all ident_ok comps) then None
  else
    let rec drop_last = function
      | [] | [_] -> []
      | x :: rest -> x :: drop_last rest in
    Some (String.concat "." (drop_last comps))

let lean_ireader_name env cref =
  Name.to_string (Path.get_name (c_env_lookup Ast.Unknown env.c_env cref).const_binding)

(* Every instance reader as (cref, projection, class), in the GLOBAL
   reader order: by the reader's unqualified lem name, then by its full
   path (a total order; equal names in two modules are distinct readers
   with distinct classes — lean_ireader_check). A malformed projection
   is refused by lean_ireader_check before this is consulted. *)
let lean_ireader_get_readers env : (Types.const_descr_ref * string * string) list =
  match !St.ireader_cache with
  | Some l -> l
  | None ->
    let l = List.filter_map (fun cref ->
        match lean_ireader_projection env cref with
        | None -> None
        | Some proj ->
          (match lean_ireader_class_of_projection proj with
           | Some cls -> Some (cref, proj, cls)
           | None ->
             let cd = c_env_lookup Ast.Unknown env.c_env cref in
             raise (Reporting_basic.err_general true cd.spec_l
               (Printf.sprintf
                 "Lean backend: 'declare {lean} reader val %s = instance `%s`': the instance text must be the PROJECTION of a one-field class, `Cls.field` — at least two dot-separated plain identifiers (no guillemets, spaces or `_root_`); the class is the prefix before the last dot (IR-proj)"
                 (lean_ireader_name env cref) proj))))
        (c_env_all_consts env.c_env) in
    let key (cref, _, _) =
      (lean_ireader_name env cref,
       Path.to_string (c_env_lookup Ast.Unknown env.c_env cref).const_binding) in
    let l = List.sort (fun a b ->
        let (na, pa) = key a and (nb, pb) = key b in
        match String.compare na nb with 0 -> String.compare pa pb | c -> c) l in
    St.ireader_cache := Some l; l

(* Keep exactly the instance readers satisfying [p], in the global order
   — the one constructor of binder lists, so every list is sorted and
   duplicate-free by construction. *)
let lean_ireader_filter env (p : Types.const_descr_ref -> bool) : Types.const_descr_ref list =
  List.filter_map (fun (cref, _, _) -> if p cref then Some cref else None)
    (lean_ireader_get_readers env)

let lean_ireader_lifted_of (cref : Types.const_descr_ref) : Types.const_descr_ref list =
  match Types.Cdmap.apply !St.ireader_lifted cref with
  | Some l -> l
  | None -> []

(* The instance readers a REFERENCE to [cref] needs in scope: the reader
   itself, the readers a consumer reads, the readers a member binds. *)
let lean_ireader_needs env (cref : Types.const_descr_ref) : Types.const_descr_ref list =
  let direct = lean_ireader_is_reader env cref in
  let cons = lean_ireader_consumer_of env cref in
  let lifted = lean_ireader_lifted_of cref in
  if not direct && cons = [] && lifted = [] then []
  else
    lean_ireader_filter env (fun r ->
        (direct && r = cref) || List.mem r cons || List.mem r lifted)

(* Guards IR-mix / IR-type / IR-inline / IR-class (instance readers) and IRC-reader /
   IRC-rep / IRC-mix (consumers): fail-closed for every marked constant
   even if unused; idempotent; run at every pre-pass entry. *)
let lean_ireader_check env =
  let readers = lean_ireader_get_readers env in
  List.iter (fun (cref, proj, _) ->
      let cd = c_env_lookup Ast.Unknown env.c_env cref in
      let cname = lean_ireader_name env cref in
      let refuse fmt = Printf.ksprintf (fun m ->
          raise (Reporting_basic.err_general true cd.spec_l m)) fmt in
      let mix which =
        refuse "Lean backend: val %s is declared both an instance reader ('declare {lean} reader val %s = instance `%s`') and {lean} %s (unsupported: IR-mix — one mechanism per val)"
          cname cname proj which in
      if Targetset.mem Target_lean cd.reader then mix "reader (explicit)";
      if Targetset.mem Target_lean cd.reader_seed then mix "reader_seed";
      if Targetset.mem Target_lean cd.supply then mix "supply";
      if Targetset.mem Target_lean cd.reader_consumer then mix "reader_consumer";
      if Targetset.mem Target_lean cd.fuel_consumer then mix "fuel_consumer";
      if lean_fuel_is_fuelled env cref then mix "fuel";
      if lean_ireader_consumer_of env cref <> [] then mix "reader_consumer ... = instance";
      (match cd.const_type.Types.t with
       | Types.Tfn ({ Types.t = Types.Tapp ([], p) }, _) when Path.compare p Path.unitpath = 0 -> ()
       | _ ->
         refuse "Lean backend: instance reader %s must have type unit -> T (the read `%s ()` becomes the projection `%s`; IR-type)"
           cname cname proj);
      (* IR-type, monomorphic: the class field has ONE type, so a reader
         whose type has free type variables (`forall 'a. unit -> 'a`)
         would be read at every instantiation from the one field — refused
         rather than left to an instantiation-dependent Lean error *)
      if cd.const_tparams <> [] || not (Types.TNset.is_empty (Types.free_vars cd.const_type)) then
        refuse "Lean backend: instance reader %s has a polymorphic type (free type variables); the class field `%s` has one type, so the reader's type must be a closed unit -> T (IR-type)"
          cname proj;
      (* IR-inline: a `let inline` body is a CR_inline Lean rep, expanded
         by the inline macro BEFORE emission — every read `r ()` would
         silently become the inlined body and never read the instance *)
      (match Target.Targetmap.apply_target cd.target_rep (Target.Target_no_ident Target.Target_lean) with
       | Some (CR_inline _) ->
         refuse "Lean backend: instance reader %s has an inline Lean representation (`let inline` / a {lean} inline body): the inline macro would replace every read `%s ()` by the body before emission, so the instance `%s` would never be read (IR-inline: drop the inline; give the reader a non-inline 'declare lean target_rep')"
           cname cname proj
       | _ -> ()))
    readers;
  (* IR-class: two readers sharing a class would bind ONE instance and
     silently read the same value. The class text is not resolved here,
     so the comparison is by the class's LAST dotted component: Lean name
     resolution (the current namespace, `open`) can make `Sw` and
     `Impl.Sw` name one class, but never changes the last component — and
     two binders of one class are legal Lean, the reads taking the
     innermost (measured on Lean 4.32.2: `def both [Impl.Sw] [Sw] … :=
     Impl.Sw.sw + Sw.sw + x` under `open Impl` gives `@both ⟨1⟩ ⟨10⟩ 0 =
     20`), so an alias would conflate SILENTLY (review F3; record §2). *)
  let last_comp cls =
    match List.rev (String.split_on_char '.' cls) with
    | x :: _ -> x
    | [] -> cls in
  let rec dup = function
    | [] -> ()
    | (c1, _, cls) :: rest ->
      (match List.find_opt (fun (_, _, cls') -> last_comp cls' = last_comp cls) rest with
       | Some (c2, _, cls') ->
         let cd = c_env_lookup Ast.Unknown env.c_env c1 in
         raise (Reporting_basic.err_general true cd.spec_l
           (if cls' = cls then
              Printf.sprintf
                "Lean backend: instance readers %s and %s share the class `%s` — both would read the ONE `[%s]` instance and silently conflate (IR-class: give each reader its own class)"
                (lean_ireader_name env c1) (lean_ireader_name env c2) cls cls
            else
              Printf.sprintf
                "Lean backend: instance readers %s and %s have the classes `%s` and `%s`, whose last components agree: Lean name resolution (the current namespace, open) may name one Lean class by both, and the two readers would then read the ONE instance and silently conflate (IR-class: classes of instance readers must differ in their last component)"
                (lean_ireader_name env c1) (lean_ireader_name env c2) cls cls'))
       | None -> dup rest) in
  dup readers;
  List.iter (fun cref ->
      match lean_ireader_consumer_of env cref with
      | [] -> ()
      | rs ->
        let cd = c_env_lookup Ast.Unknown env.c_env cref in
        let cname = lean_ireader_name env cref in
        let refuse m = raise (Reporting_basic.err_general true cd.spec_l m) in
        List.iter (fun r ->
            if not (lean_ireader_is_reader env r) then
              refuse (Printf.sprintf
                "Lean backend: 'declare {lean} reader_consumer val %s = instance %s': %s is not an instance reader (declare it with 'declare {lean} reader val %s = instance `Cls.field`'; IRC-reader)"
                cname (lean_ireader_name env r) (lean_ireader_name env r) (lean_ireader_name env r)))
          rs;
        if not (lean_has_lean_rep env cref) then
          refuse (Printf.sprintf
            "Lean backend: 'declare {lean} reader_consumer val %s = instance ...' on a val with no Lean target_rep (IRC-rep: the declare marks a hand-written implementation that binds the class itself; a generated definition's needs are computed by the fixpoint — drop the declare)"
            cname);
        if Targetset.mem Target_lean cd.reader || Targetset.mem Target_lean cd.reader_seed
           || Targetset.mem Target_lean cd.supply then
          refuse (Printf.sprintf
            "Lean backend: val %s is an instance-reader consumer and also a {lean} reader / reader_seed / supply (unsupported: IRC-mix)"
            cname))
    (c_env_all_consts env.c_env)

(* Pre-pass over one module's defs: grow St.ireader_lifted to a fixpoint.
   Val_def granularity, nested modules recursed, instances skipped (their
   methods cannot take binders: a read there is the scope error at
   emission), target_rep'd defs skipped (dead text; a hand-written rep
   that reads the class says so with `reader_consumer ... = instance`),
   reader_seed defs INCLUDED (the seed cuts explicit readers only), indreln
   blocks not lifted (a reference from a rule is the scope error) — the
   fuel pre-pass shape. *)
let lean_ireader_prepass env (ds : def list) =
  lean_ireader_check env;
  if lean_ireader_get_readers env <> [] then begin
    let target = Target.Target_no_ident Target.Target_lean in
    let rec def_infos acc (((d_aux, _), _, _) as d : def) =
      match d_aux with
      | Instance _ -> acc
      | Module (_, _, _, _, _, inner_ds, _) -> List.fold_left def_infos acc inner_ds
      | Val_def _ ->
        let defined = (add_def_entities target true empty_used_entities d).used_consts_set in
        (* IR-body: an instance reader defined by a lem body with no Lean
           target_rep would be emitted as an ordinary def (`def r [Cls]
           (u : Unit) : T := <body>`): hand-written Lean calling `r` would
           get the lem body, not the instance — refused. (Explicit readers
           have the same pre-existing gap; not changed here — record §6.) *)
        Types.Cdset.iter (fun c ->
            if lean_ireader_is_reader env c && not (lean_has_lean_rep env c) then
              let (_, l, _) = d in
              raise (Reporting_basic.err_general true l
                (Printf.sprintf
                  "Lean backend: instance reader %s ('declare {lean} reader val %s = instance `...`') has a lem definition but no Lean target_rep: it would be emitted as a def returning the lem body, so a hand-written caller of %s would not read the instance (IR-body: give it a 'declare lean target_rep', or drop the lem definition)"
                  (lean_ireader_name env c) (lean_ireader_name env c) (lean_ireader_name env c)))) defined;
        if Types.Cdset.exists (lean_has_lean_rep env) defined then acc
        else
          let used = (add_def_entities target false empty_used_entities d).used_consts_set in
          (Types.Cdset.elements defined, Types.Cdset.elements used) :: acc
      | _ -> acc in
    let infos = List.rev (List.fold_left def_infos [] ds) in
    let changed = ref true in
    while !changed do
      changed := false;
      List.iter (fun (defined, used) ->
          let needs = List.concat_map (lean_ireader_needs env) used in
          if needs <> [] then
            List.iter (fun c ->
                let cur = lean_ireader_lifted_of c in
                if not (List.for_all (fun r -> List.mem r cur) needs) then begin
                  let nw = lean_ireader_filter env (fun r -> List.mem r cur || List.mem r needs) in
                  St.ireader_lifted := Types.Cdmap.insert !St.ireader_lifted (c, nw);
                  changed := true
                end) defined) infos
    done
  end

(* ===== Supply lifting (declare {lean} supply val) =====

   Classic mechanism name: a state-passing (supply-threading)
   transform — the state analog of the reader lifting above. A supply
   constant is a counter of type [unit -> nat]; every def that
   (transitively) draws from it takes the current supply as an extra
   explicit parameter (after the reader binders) and returns the final
   supply paired with its result; a draw is
   [let (v, s') := LemLib.supplySplit s] with [supplySplit s = (s, s+1)].
   The transform is DETERMINISTIC state-passing only: it introduces
   let-bindings, tuples, and supplySplit applications — no
   nondeterminism constructor exists anywhere in its emission, and
   every position it
   cannot thread is a fail-closed generation-time error, never a
   fallback (guards G-λ, G-bare, G-inst, G-rel, G-arity, G-infix in
   the emission code below). *)

let lean_supply_is_supply env cref =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  Targetset.mem Target_lean cd.supply

let lean_supply_param_name env cref =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  String.concat "" ["_lemSupply_"; Name.to_string (Path.get_name cd.const_binding)]

(* The supply list, with the per-constant generation-time guards:
   G-type (a supply val must be [unit -> nat] — the v1 surface; a
   general element type can be added compatibly later) and the
   annotation-mix guard (supply × reader/reader_seed on one val is
   contradictory: a constant cannot be both threaded state and an
   ambient representation). *)
let lean_supply_get_params env =
  match !St.supply_params_cache with
  | Some l -> l
  | None ->
    let l =
      List.filter_map (fun cref ->
          if not (lean_supply_is_supply env cref) then None
          else begin
            let cd = c_env_lookup Ast.Unknown env.c_env cref in
            let cname = Name.to_string (Path.get_name cd.const_binding) in
            let type_ok =
              match cd.const_type.Types.t with
              | Types.Tfn (dom, cod) ->
                (match dom.Types.t, cod.Types.t with
                 | Types.Tapp ([], pd), Types.Tapp ([], pc) ->
                   Name.to_string (Path.get_name pd) = "unit"
                   && (let n = Name.to_string (Path.get_name pc) in
                       n = "nat" || n = "natural")
                 | _ -> false)
              | _ -> false in
            if not type_ok then
              raise (Reporting_basic.err_general true cd.spec_l
                (Printf.sprintf
                  "Lean backend: 'declare {lean} supply val %s' — a supply val must have type unit -> nat (the v1 supply is a counter; generalize the element type in the feature before annotating other shapes)" cname));
            if Targetset.mem Target_lean cd.reader then
              raise (Reporting_basic.err_general true cd.spec_l
                (Printf.sprintf
                  "Lean backend: val %s is declared both {lean} supply and {lean} reader (unsupported: a constant is either threaded state or an ambient reader, not both)" cname));
            if Targetset.mem Target_lean cd.reader_seed then
              raise (Reporting_basic.err_general true cd.spec_l
                (Printf.sprintf
                  "Lean backend: val %s is declared both {lean} supply and {lean} reader_seed (unsupported)" cname));
            Some (cref, lean_supply_param_name env cref)
          end)
        (c_env_all_consts env.c_env) in
    let l = List.sort (fun (_, a) (_, b) -> String.compare a b) l in
    lean_param_dup_check env "supply" l;
    St.supply_params_cache := Some l; l

(* Collect import for a qualified identifier from a target_rep.
   If the identifier has a module prefix (e.g., CerberusImpl.sizeof_ity),
   add the module to St.collected_imports for the current file. *)
(* Extract a module import from a CR_simple target rep body expression.
   Called via Backend_common.on_cr_simple_applied callback during rendering.
   Only fires for the current file's expressions — giving per-file scoping. *)
let collect_cr_simple_import (is_library : bool) (id_str : string) =
  (* Only collect imports for non-library target reps — library target reps
     reference Lean stdlib or LemLib names already available via import LemLib. *)
  if is_library then ()
  else
  match String.index_opt id_str '.' with
    | Some dot_pos when dot_pos > 0 ->
      let mod_name = String.sub id_str 0 dot_pos in
      (* Namespace heads provided by Lean's Init/LemLib import are not
         module filenames: e.g. Nat.succ must not cause `import Nat`.
         This is a syntactic convenience, not Lean name resolution; other
         namespace/module mismatches need an explicit extra_import. *)
      let prelude_namespaces =
        ["Nat"; "Int"; "Bool"; "String"; "Char"; "List"; "Option";
         "Array"; "ByteArray"; "Except"; "Sum"; "Prod"; "Unit";
         "PUnit"; "Empty"; "PEmpty"; "Ordering"; "Fin"; "Float";
         "UInt8"; "UInt16"; "UInt32"; "UInt64"; "USize";
         "Int8"; "Int16"; "Int32"; "Int64"; "ISize";
         "LemUnsupported"] in
      (* a module name: an upper-case letter, then letters, digits, `_`
         (a rep such as `(fun (p : Nat × Nat) => (p).1)` has a dot too, and
         its prefix is no module) *)
      let is_module_name m =
        String.length m > 0 && m.[0] >= 'A' && m.[0] <= 'Z'
        && String.for_all (fun c ->
            (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c = '_') m
      in
      if is_module_name mod_name &&
         not (List.mem mod_name prelude_namespaces) &&
         not (List.mem mod_name !St.collected_imports) then
        St.collected_imports := mod_name :: !St.collected_imports
    | _ -> ()

(* Extract the name string from a type/numeric variable *)
let tnvar_to_string = function
  | Typed_ast.Tn_A (_, tv, _) -> Ulib.Text.to_string tv
  | Typed_ast.Tn_N (_, nv, _) -> Ulib.Text.to_string nv

let tnvar_kind = function
  | Typed_ast.Tn_A _ -> "Type"
  | Typed_ast.Tn_N _ -> "Nat"

(* Check if a constant's Lean target rep is == or != (BEq operators).
   Returns Some true for ==, Some false for !=, None otherwise. *)
let check_beq_target_rep c_descr =
  match Target.Targetmap.apply_target c_descr.target_rep (Target.Target_no_ident Target.Target_lean) with
  | Some (CR_infix (_, _, _, ident)) ->
    (* Compare the TRIMMED rendering: lex_skips
       leak into Ident.to_string (the historical " ==" variant), so the
       raw string is a whitespace artifact any upstream rendering change
       would silently perturb. Trimming keys the semantics on the
       operator itself. *)
    let name = String.trim (Ident.to_string ident) in
    if name = "==" then Some true
    else if name = "!=" then Some false
    else None
  | _ -> None

(* Library modules live under the LemLib.* namespace (e.g. "LemLib.Set").
   User modules have no namespace prefix. *)
let is_library_module mod_name =
  let prefix = "LemLib." in
  let plen = String.length prefix in
  String.length mod_name >= plen && String.sub mod_name 0 plen = prefix

(* Convert a module name like "LemLib.Set" to a flat namespace name "Lem_Set".
   Non-library modules are unchanged. *)
let lean_ns_name mod_name =
  let prefix = "LemLib." in
  let plen = String.length prefix in
  if is_library_module mod_name then
    String.concat "" ["Lem_"; String.sub mod_name plen (String.length mod_name - plen)]
  else mod_name

let lean_qualified_name name_str =
  match !St.namespace_stack with
    | [] -> name_str
    | ns -> String.concat "." (List.rev ns @ [name_str])

(* ===== Inhabited derivation analysis (pre-pass side) =====
   Pure analysis helpers shared by the pre-pass (which computes the
   census + tier-2 plans in DECLARATION order) and the emission code
   (which only renders). Design note:
   doc/notes/2026-08-20_arc8-inhabited-threading-design.md rules 1-6. *)

(* Check if a source type references any of the given paths (mutual type detection) *)
let rec src_t_references_paths mutual_paths (s : src_t) : bool =
  match s.term with
    | Typ_wild _ | Typ_var _ | Typ_len _ -> false
    | Typ_tup seplist ->
        List.exists (src_t_references_paths mutual_paths) (Seplist.to_list seplist)
    | Typ_app (p, ts) ->
        List.exists (fun mp -> Path.compare mp p.descr = 0) mutual_paths ||
        List.exists (src_t_references_paths mutual_paths) ts
    | Typ_paren (_, inner, _) | Typ_with_sort (inner, _) ->
        src_t_references_paths mutual_paths inner
    | Typ_fn (dom, _, rng) ->
        src_t_references_paths mutual_paths dom || src_t_references_paths mutual_paths rng
    | Typ_backend (_, ts) ->
        List.exists (src_t_references_paths mutual_paths) ts

(* Check if a src_t is directly one of the mutual types (not wrapped
   in List, Option, etc.). Used for Inhabited generation: indirect
   references through containers are safe because List.default = [],
   Option.default = none, etc. — they don't evaluate the element's default. *)
let rec src_t_is_directly_mutual mutual_paths (s : src_t) : bool =
  match s.term with
    | Typ_app (id, _) ->
      List.exists (fun p -> Path.compare p id.descr = 0) mutual_paths
    | Typ_paren (_, t, _) -> src_t_is_directly_mutual mutual_paths t
    | Typ_with_sort (t, _) -> src_t_is_directly_mutual mutual_paths t
    | _ -> false

(* For mutual types, find a constructor whose args don't reference any mutual types.
   Prefers nullary constructors, then constructors with non-mutual args. *)
let find_safe_ctor_for_mutual mutual_paths ctors =
  let nullary = List.find_opt (fun (_, _, _, src_ts) ->
    Seplist.to_list src_ts = []
  ) ctors in
  match nullary with
    | Some _ -> nullary
    | None ->
      List.find_opt (fun (_, _, _, src_ts) ->
        let args = Seplist.to_list src_ts in
        not (List.exists (src_t_references_paths mutual_paths) args)
      ) ctors

(* Tier-1/tier-2 split. Tier 1 covers: non-parameterized types with a
   safe or safe-indirect
   constructor (or record/abbrev/opaque texps), and parameterized
   variants with a nullary constructor. Everything else is tier 2:
   per-constructor bounded derivation. *)
let inhabited_needs_tier2 mutual_paths ((_, tnvar_list, path, t, _)) : bool =
  if tnvar_list = [] then
    match t with
      | Te_variant (_, seplist) ->
        let ctors = Seplist.to_list seplist in
        (match find_safe_ctor_for_mutual mutual_paths ctors with
          | Some _ -> false
          | None ->
            not (List.exists (fun (_, _, _, src_ts) ->
              let args = Seplist.to_list src_ts in
              not (List.exists (src_t_is_directly_mutual [path]) args)) ctors))
      | Te_opaque ->
        (* User-module opaque types are fail-closed — no constructors to
           derive through, so tier 2 records Plan_none / Inh_none (NO
           instance, no fallback; backend-visible demands are
           generation-time errors). *)
        true
      | _ -> false
  else
    match t with
      | Te_variant (_, seplist) ->
        not (List.exists (fun (_, _, _, src_ts) ->
          Seplist.to_list src_ts = []) (Seplist.to_list seplist))
      | _ -> true

(* Derivability analysis (design note rules 2 and 4) for a
   constructor-field type. Returns Some bound-tyvar-names — the
   [Inhabited tv] bounds the field's default needs — or None (field not
   derivably inhabitable). Recursively: type variables induce a bound;
   tuples combine; function types need only an inhabitable codomain
   (fun _ => default); applied types resolve through the instance
   census (an unconditional instance is preferred, else the first
   instance entry whose demanded argument positions are derivable —
   container heads like list/maybe/fmap are unconditional, so mutual
   references shielded by them stay derivable, the
   src_t_is_directly_mutual precedent). pending = paths with NO usable
   instance at this point: the type itself plus mutual siblings not yet
   emitted (rule 4: tier 2 skips self/mutual-referential constructors;
   earlier siblings and separate earlier types resolve through their
   already-recorded instances). *)
let derive_field_bounds (pending : Path.t list) (s : src_t) : string list option =
  let union a b = a @ List.filter (fun x -> not (List.mem x a)) b in
  let rec go (s : src_t) : string list option =
    match s.term with
      | Typ_var (_, v) -> Some [Ulib.Text.to_string (Tyvar.to_rope v)]
      | Typ_len _ -> Some []
      | Typ_wild _ -> None
      | Typ_paren (_, t, _) | Typ_with_sort (t, _) -> go t
      | Typ_tup seplist ->
          List.fold_left (fun acc t ->
            match acc with
              | None -> None
              | Some a -> (match go t with
                  | None -> None
                  | Some b -> Some (union a b)))
            (Some []) (Seplist.to_list seplist)
      | Typ_fn (_, _, rng) -> go rng
      | Typ_backend (_, _) -> Some []
      | Typ_app (id, ts) ->
          let p = id.descr in
          if List.exists (fun q -> Path.compare p q = 0) pending then None
          else
            let entries = match inhabited_census_lookup p with
              | Some (_, Inh_none) -> []
              | Some (_, Inh_instances es) -> es
              | None -> lean_builtin_inhabited_entries p
            in
            if List.exists (fun e -> e = []) entries then Some []
            else
              List.fold_left (fun acc e ->
                match acc with
                  | Some _ -> acc
                  | None ->
                    List.fold_left (fun acc2 i ->
                      match acc2 with
                        | None -> None
                        | Some a ->
                          (match List.nth_opt ts i with
                            | None -> None
                            | Some t -> (match go t with
                                | None -> None
                                | Some b -> Some (union a b))))
                      (Some []) e)
                None entries
  in go s

(* Derivability of a list of field types: all derivable, bounds unioned. *)
let derive_fields_bounds (pending : Path.t list) (ss : src_t list) : string list option =
  List.fold_left (fun acc t ->
    match acc with
      | None -> None
      | Some a -> (match derive_field_bounds pending t with
          | None -> None
          | Some b -> Some (a @ List.filter (fun x -> not (List.mem x a)) b)))
    (Some []) ss

(* Bound tyvar names -> parameter positions (for the census). *)
let inhabited_bounds_to_positions tnvar_list (bounds : string list) : int list =
  let rec go i = function
    | [] -> []
    | tv :: rest ->
      let tail = go (i + 1) rest in
      if List.mem (tnvar_to_string tv) bounds then i :: tail else tail
  in go 0 tnvar_list

(* Tier-2 plan for one type: one entry per usable
   constructor, in declaration order; Plan_none = fail-closed. *)
let inhabited_tier2_compute (pending : Path.t list) ((_, _, _, t, _)) : inh_plan =
  match t with
    | Te_variant (_, seplist) ->
      let ctors = Seplist.to_list seplist in
      let usable = List.concat (List.mapi (fun i (_, _, _, src_ts) ->
        match derive_fields_bounds pending (Seplist.to_list src_ts) with
          | Some bounds -> [(i, bounds)]
          | None -> []) ctors) in
      if usable = [] then Plan_none else Plan_variant usable
    | Te_record (_, _, fields, _) ->
      (match derive_fields_bounds pending
               (List.map (fun (_, _, _, s) -> s) (Seplist.to_list fields)) with
        | Some bounds -> Plan_record bounds
        | None -> Plan_none)
    | _ ->
      (* Te_opaque with parameters: no constructors to derive through.
         Te_abbrev never reaches tier 2 (skip_inhabited filters it). *)
      Plan_none

(* skip_inhabited_for_type, callable outside the backend functor *)
let skip_inhabited_for_type_env env t path =
  let l = Ast.Trans (false, "skip_inhabited_for_type", None) in
  let td = Types.type_defs_lookup l env.t_env path in
  (* Skip if declared with 'skip instances' for Lean *)
  Target.Targetset.mem Target.Target_lean td.Types.type_skip_instances ||
  match t with
    | Te_abbrev _ -> true
    | _ ->
      Target.Targetmap.apply_target td.Types.type_target_rep
        (Target.Target_no_ident Target.Target_lean) <> None

(* Inhabited pre-pass: computes the instance census and the
   tier-2 derivation plans for a whole file IN DECLARATION ORDER,
   before emission (which walks definitions with fold_right, i.e.
   last-to-first side effects — the lean_reader_prepass /
   St.mutual_records precedent). Mirrors the emission dispatch
   exactly: Seplist.length > 1 -> the mutual machinery (all tier-1
   instances of a block precede all its tier-2 instances), otherwise
   the single-type path. The census persists across files (types from
   earlier modules resolve through it; lem processes modules in
   dependency order in one invocation). *)
let lean_inhabited_prepass env (ds : def list) =
  let census_name path = Name.to_string (Path.get_name path) in
  let record_tier2 pending (((_, _), tnvar_list, path, _, _) as td) =
    let plan = inhabited_tier2_compute pending td in
    inhabited_plan_add path plan;
    (if inhabited_census_debug then
      Printf.eprintf "PLAN %s: %s\n%!" (Path.to_string path)
        (match plan with
          | Plan_none -> "NONE"
          | Plan_record b -> Printf.sprintf "record[%s]" (String.concat "," b)
          | Plan_variant l -> String.concat ";" (List.map (fun (i, b) ->
              Printf.sprintf "ctor%d[%s]" i (String.concat "," b)) l)));
    match plan with
      | Plan_none -> inhabited_census_add path (census_name path) Inh_none
      | Plan_record bounds ->
        inhabited_census_add path (census_name path)
          (Inh_instances [inhabited_bounds_to_positions tnvar_list bounds])
      | Plan_variant usable ->
        inhabited_census_add path (census_name path)
          (Inh_instances (List.map (fun (_, b) ->
            inhabited_bounds_to_positions tnvar_list b) usable))
  in
  let process_block defs =
    let multi = Seplist.length defs > 1 in
    let ts_list = Seplist.to_list defs in
    let is_lib = is_library_module !St.current_module_name in
    let ts_list = if is_lib then List.filter (fun (_, _, _, t, _) -> t <> Te_opaque) ts_list else ts_list in
    let non_abbrev = List.filter (fun (_, _, _, t, _) ->
      match t with Te_abbrev _ -> false | _ -> true) ts_list in
    let active = List.filter (fun (_, _, path, t, _) ->
      not (skip_inhabited_for_type_env env t path)) ts_list in
    if multi then begin
      let mutual_paths = List.map (fun (_, _, path, _, _) -> path) non_abbrev in
      let tier1, tier2 = List.partition
        (fun td -> not (inhabited_needs_tier2 mutual_paths td)) active in
      (* Tier-1 census first: in the emitted file every tier-1 instance
         of a block precedes every tier-2 instance of that block. *)
      List.iter (fun (_, _, path, _, _) ->
        inhabited_census_add path (census_name path) (Inh_instances [[]])) tier1;
      let tier2_paths = List.map (fun (_, _, path, _, _) -> path) tier2 in
      ignore (List.fold_left (fun pending ((_, _, path, _, _) as td) ->
        record_tier2 pending td;
        List.filter (fun p -> Path.compare p path <> 0) pending)
        tier2_paths tier2)
    end else
      List.iter (fun ((_, _, path, _, _) as td) ->
        if inhabited_needs_tier2 [path] td then record_tier2 [path] td
        else inhabited_census_add path (census_name path) (Inh_instances [[]]))
        active
  in
  let rec walk (((d_aux, _), _, _) : def) =
    match d_aux with
    | Module (_, _, _, _, _, inner_ds, _) -> List.iter walk inner_ds
    | Type_def (_, defs) -> process_block defs
    | _ -> ()
  in List.iter walk ds

(* ===== failwith -> failwithI + selective [Inhabited] threading =====
   Design note doc/notes/2026-08-20_arc8-inhabited-threading-design.md,
   section S2 (rules 1-6). EVERY failure site (failwith-mapped constants,
   plus the L_undefined literals from pattern compilation) emits an
   Inhabited-backed failwithI (L_undefined too mirrors OCaml's
   `failwith m`, src/backend.ml:864) — never a silent default. Sites
   whose type mentions free type variables that are
   NOT discharged by the instance census induce [Inhabited tv]
   instance-implicit binders on the ENCLOSING def's signature, computed
   here as a monotone fixpoint over the call graph (a caller that passes
   its own free tyvar into a threaded position inherits the binder).
   Instance-implicit binders need no call-site edits;
   the pass edits signatures only. Fail-closed guards (rules 3-4):
   - a tyvar failure site inside a generated instance method (binders
     impossible there) is a generation-time error naming the instance;
   - a demand on a tyvar that does not occur in the enclosing def's
     TYPE (a phantom tyvar — the undetermined function-field shape) is a
     generation-time error naming the def and the tyvar. *)

(* Expression destructor context for the pre-pass walk (no checking, no
   renaming — the same defs are re-walked by emission). *)
module ExpW = Exps_in_context(struct let env_opt = None let avoid = None end)

(* Every name BOUND anywhere inside an expression — pattern binders of
   funs/matches/lets/do-lines/quantifiers, compiled or not. The
   reserved-name scan must cover CLAUSE BODIES: a body binder named
   lemFuel/_lemReader_* silently shadows the synthesized binder at the
   self-call/injection sites just as a parameter does (a parameter-only
   scan once let such a program compile and run wrong). Conservative
   over-collection is fine: the consumer only greps for the reserved
   names. *)
let rec exp_bound_names (e : exp) : string list =
  let pat_names p =
    List.map (fun a -> Name.to_string (Name.strip_lskip a.term))
      (Pattern_syntax.pat_vars_src p) in
  let seplist_exps sl = Seplist.to_list sl in
  match ExpW.exp_to_term e with
  | Var _ | Backend _ | Nvar_e _ | Constant _ | Lit _ -> []
  | Fun (_, ps, _, e1) -> List.concat_map pat_names ps @ exp_bound_names e1
  | Function (_, arms, _) ->
    List.concat_map (fun (p, _, e1, _) -> pat_names p @ exp_bound_names e1)
      (Seplist.to_list arms)
  | App (e1, e2) -> exp_bound_names e1 @ exp_bound_names e2
  | Infix (e1, e2, e3) ->
    exp_bound_names e1 @ exp_bound_names e2 @ exp_bound_names e3
  | Record (_, fes, _) | Recup (_, _, _, fes, _) ->
    let base = (match ExpW.exp_to_term e with
      | Recup (_, e0, _, _, _) -> exp_bound_names e0 | _ -> []) in
    base @ List.concat_map (fun (_, _, e1, _) -> exp_bound_names e1)
      (Seplist.to_list fes)
  | Field (e1, _, _) -> exp_bound_names e1
  | Vector (_, es, _) | Tup (_, es, _) | List (_, es, _) | Set (_, es, _) ->
    List.concat_map exp_bound_names (seplist_exps es)
  | VectorSub (e1, _, _, _, _, _) | VectorAcc (e1, _, _, _) -> exp_bound_names e1
  | Case (_, _, e0, _, arms, _) ->
    exp_bound_names e0 @
    List.concat_map (fun (p, _, e1, _) -> pat_names p @ exp_bound_names e1)
      (Seplist.to_list arms)
  | Typed (_, e1, _, _, _) | Paren (_, e1, _) | Begin (_, e1, _) ->
    exp_bound_names e1
  | Let (_, (lb, _), _, e1) ->
    (match lb with
     | Let_val (p, _, _, e2) -> pat_names p @ exp_bound_names e2
     | Let_fun (n, ps, _, _, e2) ->
       Name.to_string (Name.strip_lskip n.term)
       :: List.concat_map pat_names ps @ exp_bound_names e2)
    @ exp_bound_names e1
  | If (_, e1, _, e2, _, e3) ->
    exp_bound_names e1 @ exp_bound_names e2 @ exp_bound_names e3
  | Setcomp (_, e1, _, e2, _, ns) ->
    NameSet.fold (fun n acc -> Name.to_string n :: acc) ns []
    @ exp_bound_names e1 @ exp_bound_names e2
  | Comp_binding (_, _, e1, _, _, qbs, _, e2, _) ->
    List.concat_map qb_bound_names qbs @ exp_bound_names e1 @ exp_bound_names e2
  | Quant (_, qbs, _, e1) ->
    List.concat_map qb_bound_names qbs @ exp_bound_names e1
  | Do (_, _, dls, _, e1, _, _) ->
    List.concat_map (fun (Do_line (p, _, e2, _)) ->
      List.map (fun a -> Name.to_string (Name.strip_lskip a.term))
        (Pattern_syntax.pat_vars_src p) @ exp_bound_names e2) dls
    @ exp_bound_names e1
and qb_bound_names = function
  | Qb_var n -> [Name.to_string (Name.strip_lskip n.term)]
  | Qb_restr (_, _, p, _, e, _) ->
    List.map (fun a -> Name.to_string (Name.strip_lskip a.term))
      (Pattern_syntax.pat_vars_src p) @ exp_bound_names e


(* ===== The structural-parameter analysis (declare {lean} structural val;
   mechanism comment at lean_is_structural) =====

   A variable's LEVEL relative to the definition's parameters: SL_exact i
   = the i-th parameter itself (or an alias of it); SL_strict i = bound by
   a constructor pattern (P_const/P_cons/P_list/P_record/P_num_add, or a
   tuple INSIDE one of those) in a match whose scrutinee is at level
   exact/strict i — a strict structural subterm of parameter i. A tuple
   pattern at the top of a match on a tuple-typed variable does NOT
   descend (its components are of other types; Lean's checker agrees), but
   a match on a tuple OF variables binds component-wise (the renderer
   emits it as a multi-discriminant match); a record-field projection is
   NOT tracked (see `level`). Shadowing removes a name;
   `let x = y` aliases a tracked variable. Every application whose head is
   a member of the block is a CALL (callee, argument levels, location); a
   member referenced in any other position (passed to a higher-order
   function, partially applied under a lambda) is refused outright —
   Lean's structural checker cannot eliminate such a recursive
   application either ("failed to eliminate recursive application"). *)
type struct_level = SL_exact of int | SL_strict of int

(* the status of one argument at a recursive call *)
type struct_arg =
  | SA_nonvar                      (* not a variable (an application, a literal, …) *)
  | SA_untracked of string         (* a variable bound outside the structural chain *)
  | SA_level of struct_level

type struct_call = {
  sc_callee : Types.const_descr_ref;
  sc_args : struct_arg list;
  sc_locn : Ast.l;
}

exception Structural_refused of Ast.l * string

let struct_level_idx = function SL_exact i | SL_strict i -> i

let rec lean_strip_pat (p : pat) : pat_aux =
  match p.term with
  | P_paren (_, p', _) | P_typ (_, p', _, _, _) -> lean_strip_pat p'
  | t -> t

let lean_structural_calls (members : (Types.const_descr_ref * string) list)
    (env0 : (string * struct_level) list) (body : exp) : struct_call list =
  let calls = ref [] in
  let nm n = Name.to_string (Name.strip_lskip n) in
  let pat_names p =
    List.map (fun a -> nm a.term) (Pattern_syntax.pat_vars_src p) in
  let remove names env = List.filter (fun (n, _) -> not (List.mem n names)) env in
  let rec strip e = match ExpW.exp_to_term e with
    | Paren (_, e', _) | Typed (_, e', _, _, _) | Begin (_, e', _) -> strip e'
    | _ -> e in
  (* NOT tracked: a record-field projection `c.tail` of a tracked variable.
     lem compiles a record pattern into a match on the projections
     (`match c.head, c.tail with | _, Just c' -> …`), and Lean's structural
     checker cannot eliminate a recursive application through a projection
     — measured (structural-declare record §3): with a permissive rule
     here the Lean build refused `failed to infer structural recursion:
     Cannot use parameter c: failed to eliminate recursive application
     chain_len c'`. The analysis mirrors the checker. *)
  let level env e = match ExpW.exp_to_term (strip e) with
    | Var v -> List.assoc_opt (nm v) env
    | _ -> None in
  let arg_status env e = match ExpW.exp_to_term (strip e) with
    | Var v -> (match List.assoc_opt (nm v) env with
        | Some l -> SA_level l
        | None -> SA_untracked (nm v))
    | _ -> SA_nonvar in
  let rec bind_pat top l env (p : pat) =
    let under = if top then l else SL_strict (struct_level_idx l) in
    match p.term with
    | P_var n | P_var_annot (n, _) -> (nm n, under) :: env
    | P_wild _ | P_lit _ -> env
    | P_num_add ((n, _), _, _, _) -> (nm n, SL_strict (struct_level_idx l)) :: env
    | P_as (_, p', _, (n, _), _) -> bind_pat top l ((nm n, under) :: env) p'
    | P_typ (_, p', _, _, _) | P_paren (_, p', _) -> bind_pat top l env p'
    | P_tup (_, ps, _) ->
      if top then env
      else List.fold_left (bind_pat false l) env (Seplist.to_list ps)
    | P_const (_, ps) | P_backend (_, _, _, ps) | P_vectorC (_, ps, _) ->
      List.fold_left (bind_pat false l) env ps
    | P_record (_, fps, _) ->
      List.fold_left (fun env (_, _, p') -> bind_pat false l env p') env (Seplist.to_list fps)
    | P_vector (_, ps, _) | P_list (_, ps, _) ->
      List.fold_left (bind_pat false l) env (Seplist.to_list ps)
    | P_cons (p1, _, p2) -> bind_pat false l (bind_pat false l env p1) p2 in
  let qb_names = function
    | Qb_var n -> [nm n.term]
    | Qb_restr (_, _, p, _, _, _) -> pat_names p in
  let is_member e = match ExpW.exp_to_term e with
    | Constant c -> List.mem_assoc c.descr members
    | _ -> false in
  let member_name e = match ExpW.exp_to_term e with
    | Constant c -> List.assoc c.descr members
    | _ -> "" in
  let member_of e = match ExpW.exp_to_term e with
    | Constant c -> c.descr
    | _ -> assert false in
  let rec walk env (e : exp) : unit =
    match ExpW.exp_to_term e with
    | Var _ | Lit _ | Nvar_e _ | Backend _ -> ()
    | Constant _ when is_member e ->
      raise (Structural_refused (Typed_ast.exp_to_locn e,
        Printf.sprintf "a self-reference to %s in non-call position (passed as a value, e.g. to a higher-order function such as List.map/List.all): Lean's structural checker cannot eliminate such a recursive application — write the traversal as an explicit recursion (a list-walking sibling in the same mutual block)" (member_name e)))
    | Constant _ -> ()
    | App _ ->
      let (head, args) = Typed_ast_syntax.strip_app_exp e in
      if is_member head then
        calls := { sc_callee = member_of head;
                   sc_args = List.map (arg_status env) args;
                   sc_locn = Typed_ast.exp_to_locn e } :: !calls
      else walk env head;
      List.iter (walk env) args
    | Infix (e1, op, e2) ->
      if is_member op then
        calls := { sc_callee = member_of op;
                   sc_args = [arg_status env e1; arg_status env e2];
                   sc_locn = Typed_ast.exp_to_locn e } :: !calls
      else walk env op;
      walk env e1; walk env e2
    | Fun (_, ps, _, body) -> walk (remove (List.concat_map pat_names ps) env) body
    | Function (_, arms, _) ->
      List.iter (fun (p, _, body, _) -> walk (remove (pat_names p) env) body)
        (Seplist.to_list arms)
    | Case (_, _, scrut, _, arms, _) ->
      walk env scrut;
      let scrut' = strip scrut in
      let tup_levels = match ExpW.exp_to_term scrut' with
        | Tup (_, es, _) -> Some (List.map (level env) (Seplist.to_list es))
        | _ -> None in
      let one_level = level env scrut' in
      List.iter (fun (p, _, body, _) ->
          let env0 = remove (pat_names p) env in
          let env1 = match tup_levels, one_level with
            | Some ls, _ ->
              (match lean_strip_pat p with
               | P_tup (_, ps, _) when List.length ls = Seplist.length ps ->
                 List.fold_left2 (fun env l p' ->
                     match l with Some l -> bind_pat true l env p' | None -> env)
                   env0 ls (Seplist.to_list ps)
               | _ -> env0)
            | None, Some l -> bind_pat true l env0 p
            | None, None -> env0 in
          walk env1 body)
        (Seplist.to_list arms)
    | Typed (_, e', _, _, _) | Paren (_, e', _) | Begin (_, e', _) -> walk env e'
    | Let (_, (lb, _), _, body) ->
      (match lb with
       | Let_val (p, _, _, rhs) ->
         walk env rhs;
         let env0 = remove (pat_names p) env in
         let env1 = match lean_strip_pat p, level env rhs with
           | (P_var n | P_var_annot (n, _)), Some l -> (nm n, l) :: env0
           | _ -> env0 in
         walk env1 body
       | Let_fun (n, ps, _, _, rhs) ->
         let fname = nm n.term in
         walk (remove (fname :: List.concat_map pat_names ps) env) rhs;
         walk (remove [fname] env) body)
    | Tup (_, es, _) | List (_, es, _) | Vector (_, es, _) | Set (_, es, _) ->
      List.iter (walk env) (Seplist.to_list es)
    | Record (_, fes, _) ->
      List.iter (fun (_, _, e', _) -> walk env e') (Seplist.to_list fes)
    | Recup (_, e0, _, fes, _) ->
      walk env e0;
      List.iter (fun (_, _, e', _) -> walk env e') (Seplist.to_list fes)
    | Field (e', _, _) -> walk env e'
    | VectorSub (e', _, _, _, _, _) | VectorAcc (e', _, _, _) -> walk env e'
    | If (_, e1, _, e2, _, e3) -> walk env e1; walk env e2; walk env e3
    | Setcomp (_, e1, _, e2, _, ns) ->
      let env' = remove (NameSet.fold (fun n acc -> Name.to_string n :: acc) ns []) env in
      walk env' e1; walk env' e2
    | Comp_binding (_, _, e1, _, _, qbs, _, e2, _) ->
      let env' = remove (List.concat_map qb_names qbs) env in
      walk env' e1; walk env' e2
    | Quant (_, qbs, _, e1) -> walk (remove (List.concat_map qb_names qbs) env) e1
    | Do (_, _, dls, _, e1, _, _) ->
      let env' = List.fold_left (fun env (Do_line (p, _, rhs, _)) ->
          walk env rhs; remove (pat_names p) env) env dls in
      walk env' e1 in
  walk env0 body;
  List.rev !calls

(* The designated structural parameter of every member of a block (a
   single self-recursive definition, or every member of a truly mutual
   block): an assignment member -> parameter position such that at every
   call from member f to member g, g's designated argument is at level
   SL_strict (f's designated position). The search is exhaustive over the
   named parameters (blocks are small); the first assignment in
   parameter order wins — Lean's own inference tries parameters in the
   same order. On failure the refusal names, for each named parameter of
   the first member, the first call that breaks it. *)
let lean_structural_assign
    (members : (Types.const_descr_ref * string * pat list * exp * Ast.l) list)
    : (Types.const_descr_ref * int) list =
  let param_name pats i = match List.nth_opt pats i with
    | Some p -> (match lean_strip_pat p with
        | P_var n | P_var_annot (n, _) -> Some (Name.to_string (Name.strip_lskip n))
        | _ -> None)
    | None -> None in
  let crefs = List.map (fun (c, name, _, _, _) -> (c, name)) members in
  let infos = List.map (fun (c, name, pats, body, l) ->
      let env = List.concat (List.mapi (fun i _ ->
          match param_name pats i with
          | Some n -> [(n, SL_exact i)]
          | None -> []) pats) in
      let calls = lean_structural_calls crefs env body in
      (c, name, pats, calls, l)) members in
  let cands (_, _, pats, _, _) =
    List.filter (fun i -> param_name pats i <> None)
      (List.init (List.length pats) (fun i -> i)) in
  let call_ok assign pc sc =
    match List.assoc_opt sc.sc_callee assign with
    | None -> false
    | Some pg ->
      (match List.nth_opt sc.sc_args pg with
       | Some (SA_level (SL_strict i)) -> i = pc
       | _ -> false) in
  let ok assign =
    List.for_all (fun (c, _, _, calls, _) ->
        let pc = List.assoc c assign in
        List.for_all (call_ok assign pc) calls) infos in
  let rec search acc = function
    | [] -> let a = List.rev acc in if ok a then Some a else None
    | ((c, _, _, _, _) as m) :: rest ->
      List.fold_left (fun found i ->
          match found with
          | Some _ -> found
          | None -> search ((c, i) :: acc) rest)
        None (cands m) in
  match search [] infos with
  | Some a -> a
  | None ->
    let (c0, name0, pats0, calls0, l0) = List.hd infos in
    let describe_arg pats_of_callee pc pg sc =
      match List.nth_opt sc.sc_args pg with
      | None -> Printf.sprintf "the call supplies fewer than %d arguments" (pg + 1)
      | Some SA_nonvar -> "the argument is not a variable"
      | Some (SA_untracked v) ->
        Printf.sprintf "the argument `%s` is a variable that is not bound by a constructor pattern on that parameter (bound by a lambda or let, or by a match on a computed scrutinee — note that lem compiles a record pattern into a match on field projections, which Lean's structural checker cannot see through)" v
      | Some (SA_level (SL_exact i)) when i = pc -> "the argument is the parameter itself (not a strict subterm)"
      | Some (SA_level (SL_exact i)) | Some (SA_level (SL_strict i)) ->
        Printf.sprintf "the argument is (a subterm of) parameter %s, not of this one"
          (match param_name pats_of_callee i with Some n -> n | None -> string_of_int i) in
    let per_param = List.filter_map (fun i ->
        match param_name pats0 i with
        | None -> None
        | Some pname ->
          (* the assignment that designates position i for the first
             member and its own position for every sibling call *)
          let first_bad = List.find_opt (fun sc ->
              not (call_ok [(c0, i)] i sc) || sc.sc_callee <> c0) calls0 in
          (match first_bad with
           | None when calls0 = [] -> Some (Printf.sprintf "  parameter %s: the definition makes no call to itself" pname)
           | None -> None
           | Some sc when sc.sc_callee <> c0 ->
             Some (Printf.sprintf "  parameter %s: a call to a mutual sibling at %s has no structural position consistent with the block"
                     pname (Reporting_basic.loc_to_string true sc.sc_locn))
           | Some sc ->
             Some (Printf.sprintf "  parameter %s: at the self-call %s, %s" pname
                     (Reporting_basic.loc_to_string true sc.sc_locn)
                     (describe_arg pats0 i i sc))))
        (List.init (List.length pats0) (fun i -> i)) in
    let plural = if List.length members > 1 then " (mutual block: every member must recurse structurally on one of its parameters, and every cross-call must pass a strict subterm)" else "" in
    raise (Structural_refused (l0,
      Printf.sprintf "no parameter of %s is passed a strict structural subterm (a variable bound by a constructor pattern on that parameter) at every recursive call%s:\n%s"
        name0 plural
        (if per_param = [] then "  (no parameter of this definition is a plain variable)"
         else String.concat "\n" per_param)))

(* Types.t analog of derive_field_bounds: which tyvars must carry an
   [Inhabited tv] bound for the type to be synthesizable from the
   instance census. Some [] = discharged unconditionally; Some tvs =
   discharged given [Inhabited tv] for each; None = not derivable at all
   (an Inh_none-census type in a demanded position). Type abbreviations
   are head-normalized away first. *)
let rec typ_inhabited_bounds (d : Types.type_defs) (t : Types.t) : string list option =
  let union a b = a @ List.filter (fun x -> not (List.mem x a)) b in
  let t = Types.head_norm d t in
  match t.Types.t with
    | Types.Tvar v -> Some [Ulib.Text.to_string (Tyvar.to_rope v)]
    | Types.Tne _ -> Some []
    | Types.Tuvar _ -> Some []
    | Types.Tfn (_, cod) -> typ_inhabited_bounds d cod
    | Types.Tbackend _ -> Some []
    | Types.Ttup ts ->
      List.fold_left (fun acc t' ->
        match acc with
          | None -> None
          | Some a -> (match typ_inhabited_bounds d t' with
              | None -> None
              | Some b -> Some (union a b)))
        (Some []) ts
    | Types.Tapp (ts, p) ->
      let entries = match inhabited_census_lookup p with
        | Some (_, Inh_none) -> []
        | Some (_, Inh_instances es) -> es
        | None -> lean_builtin_inhabited_entries p
      in
      if List.exists (fun e -> e = []) entries then Some []
      else
        List.fold_left (fun acc e ->
          match acc with
            | Some _ -> acc
            | None ->
              List.fold_left (fun acc2 i ->
                match acc2 with
                  | None -> None
                  | Some a ->
                    (match List.nth_opt ts i with
                      | None -> None
                      | Some t' -> (match typ_inhabited_bounds d t' with
                          | None -> None
                          | Some b -> Some (union a b))))
                (Some []) e)
          None entries

(* ===== Derived structural comparisons for mutual blocks =====
   Shape analysis for constructor-field types, deciding how a derived
   BEq/compare body compares each field. Computed on SEMANTIC types
   (Types.t, head-normalized) so type abbreviations can never hide a
   mutual-sibling reference (the src_t_has_fn abbrev lesson). *)
type cmp_shape =
  | CSleaf                                   (* no sibling inside: instance-based == / Ord.compare *)
  | CSsibling of string                      (* Lean name: mutual call to <name>.beq_derived / .compare_derived *)
  | CStuple of cmp_shape list                (* destructure, compare componentwise *)
  | CSlist of Types.t * cmp_shape            (* element type + element shape: mutual list helper *)
  | CSoption of Types.t * cmp_shape          (* mutual option helper *)
  | CSsum of (Types.t * cmp_shape) * (Types.t * cmp_shape)  (* mutual sum helper *)
  | CSbad of string                          (* underivable: reason (fail-closed, type keeps its residual) *)
  | CSfn                                     (* function-typed field: comparing it panics as OCaml's
                                                polymorphic compare raises "compare: functional value" on closures *)

(* Does the (head-normalized) type reference any of the given paths? *)
let rec lean_typ_refs_paths (d : Types.type_defs) (paths : Path.t list) (t : Types.t) : bool =
  let t = Types.head_norm d t in
  match t.Types.t with
    | Types.Tvar _ | Types.Tne _ | Types.Tuvar _ -> false
    | Types.Tfn (a, b) -> lean_typ_refs_paths d paths a || lean_typ_refs_paths d paths b
    | Types.Ttup ts -> List.exists (lean_typ_refs_paths d paths) ts
    | Types.Tbackend (ts, _) -> List.exists (lean_typ_refs_paths d paths) ts
    | Types.Tapp (ts, p) ->
      List.exists (fun q -> Path.compare p q = 0) paths ||
      List.exists (lean_typ_refs_paths d paths) ts

(* Does the (head-normalized) type contain a function type anywhere? *)
and lean_typ_has_fn (d : Types.type_defs) (t : Types.t) : bool =
  let t = Types.head_norm d t in
  match t.Types.t with
    | Types.Tfn _ -> true
    | Types.Ttup ts | Types.Tbackend (ts, _) | Types.Tapp (ts, _) -> List.exists (lean_typ_has_fn d) ts
    | Types.Tvar _ | Types.Tne _ | Types.Tuvar _ -> false

(* Compute the comparison shape of a field type.
   derived: the mutual siblings currently in the derived set (path ->
   Lean name); residual: sibling paths OUTSIDE the derived set (their
   instances are the loud residuals, so a reference makes this type
   underivable — underivability propagates rather than routing a "real"
   body through a residual instance). Containers with a Lean-instance
   comparison story (list, maybe, either, tuples) recurse; any other head
   over a sibling is fail-closed CSbad. *)
let rec lean_cmp_shape (d : Types.type_defs) (derived : (Path.t * string) list)
    (residual : Path.t list) (t : Types.t) : cmp_shape =
  let all_paths = List.map fst derived @ residual in
  (* A field type containing a function type is compared
     structurally down to the function (OCaml's polymorphic compare raises
     only when it REACHES a closure: `GOT []` compares fine). *)
  if not (lean_typ_refs_paths d all_paths t) && not (lean_typ_has_fn d t) then CSleaf
  else
    let bad_of = function CSbad r -> Some r | _ -> None in
    let t' = Types.head_norm d t in
    match t'.Types.t with
      | Types.Tfn _ -> CSfn
      | Types.Ttup ts ->
        let shs = List.map (lean_cmp_shape d derived residual) ts in
        (match List.find_map bad_of shs with
          | Some r -> CSbad r
          | None -> CStuple shs)
      | Types.Tapp (ts, p) ->
        (match List.find_opt (fun (q, _) -> Path.compare p q = 0) derived with
          | Some (_, name) ->
            if List.exists (lean_typ_refs_paths d all_paths) ts
            then CSbad "mutual type applied to mutual-referencing arguments"
            else CSsibling name
          | None ->
            if List.exists (fun q -> Path.compare p q = 0) residual then
              CSbad "reference to a mutual sibling outside the derived set"
            else
              (match Name.to_string (Path.get_name p), ts with
                | "list", [e] ->
                  let sh = lean_cmp_shape d derived residual e in
                  (match bad_of sh with Some r -> CSbad r | None -> CSlist (e, sh))
                | "maybe", [e] ->
                  let sh = lean_cmp_shape d derived residual e in
                  (match bad_of sh with Some r -> CSbad r | None -> CSoption (e, sh))
                | "either", [l; r] ->
                  let shl = lean_cmp_shape d derived residual l in
                  let shr = lean_cmp_shape d derived residual r in
                  (match bad_of shl, bad_of shr with
                    | Some r, _ | _, Some r -> CSbad r
                    | None, None -> CSsum ((l, shl), (r, shr)))
                | n, _ -> CSbad (Printf.sprintf "mutual reference or function type under unsupported head '%s'" n)))
      | _ -> CSbad "unexpected shape"

let lean_cmp_shape_is_bad = function CSbad _ -> true | _ -> false

(* ===== Backend-derived computable SIZE functions =====

   Classic mechanism name: a STRUCTURAL SIZE (the term-size measure of a
   nested inductive), derived by the backend for every recursive block of
   generated inductive types and emitted right after the block, in the
   type's own module:

       def t.lemSize (sizex_ : t) : Nat := match sizex_ with
         | .C x1 x2 => 1 + s.lemSize x1 + t.lemSize_aux1 x2    -- one arm per constructor
         …
       termination_by structural sizex_

   Why it exists: a `declare {lean} fuel_measure val` over a type defined
   in the SAME module as the measured function cannot be a hand-written
   Lean function (that module would have to import the generated one — a
   cycle), and Lean's automatic `sizeOf` is NONCOMPUTABLE (`List._sizeOf_inst
   … has no executable code`, measured), while a
   measured wrapper must EXECUTE. So the backend derives the computable
   size itself, in the derived-comparison machinery's shape (one mutual
   block per type block, list/option/sum helpers per container element
   type, `termination_by structural` everywhere — the kernel computes
   through it, `decide` on closed terms).

   The measure names it as `lemSize x` (x a parameter; the backend
   resolves x's type to its size function: `lemSize c` ↦ `ctype.lemSize c`)
   or, explicitly, as the qualified global `ctype.lemSize c`.

   Size semantics (documented in the manual): every constructor node of
   the block's types counts 1; every non-nullary constructor of a
   supported container counts 1 (`::`, `Some`, `Sum.inl`, `Sum.inr`) and
   the nullary ones (`[]`, `none`) 0; tuples are transparent (component
   sizes summed); every other field is a LEAF counting 0 — a type
   variable (a size over `'a` cannot recurse into `'a`), a base type, a
   type of another block (its own size function, if any, is a separate
   measure the user may add: `t.lemSize x + u.lemSize y`), a function
   type, or a sibling under an unsupported head (`set t`, a user type
   applied to `t` — NOT counted; a recursion through such a field is not
   bounded by this size, and the sufficiency obligation is where that
   shows). A size bounds RECURSION DEPTH through the block's own
   constructors and the supported containers, which is what a fuel
   measure needs; a leaf's contribution is irrelevant to that bound.

   Emission policy: EVERY recursive block (some constructor field reaches
   a sibling through tuples/list/maybe/either) of a non-library module
   gets its size functions — on-demand emission is impossible in general
   because the measure that needs a size may live in another module
   generated by a LATER lem invocation (the test suite generates each file
   separately; cerberus's `Defacto_memory_aux` measures over
   `Defacto_memory_types`), and a Lean-only declare on the type side
   (`declare {lean} size type t`) was rejected as a second knob the user
   must remember (record §2 lists the alternatives and the measured output
   cost). Non-recursive types have the constant size 1 — no function is
   emitted (a measure over a constant is the magic value FM-const refuses),
   and `lemSize x` on such a type is refused at generation with the reason.
   Not derived (refused with the reason at a `lemSize` use): library types,
   target_rep'd types (they are abbrevs), opaque types, heterogeneous
   (Type-1, indexed) mutual blocks.

   Fail-closed: a constructor or record field of the block named `lemSize`
   or `lemSize_aux…` collides with the derived names (`t.lemSize` is in
   the type's namespace, as constructors are) and is refused at
   generation; `lemSize` in a measure must be applied directly to a
   parameter (`lemSize x`), whose type must be a derived-size type.

   The census below is computed by lean_size_prepass over EVERY
   typechecked module of the invocation (the inhabited census's shape,
   lean_analysis_prepass_all), so a measure can name a type from an
   imported module; the emission (generate_lem_size, in the functor) and
   the census agree because both run lean_size_block on the same block. *)

(* The size shape of a field type: the derived-comparison shape with every
   underivable/unsupported case a LEAF (a size never fails — it just does
   not count what it cannot reach). *)
let rec lean_size_shape (d : Types.type_defs) (siblings : (Path.t * string) list) (t : Types.t) : cmp_shape =
  let paths = List.map fst siblings in
  if not (lean_typ_refs_paths d paths t) then CSleaf
  else
    let t' = Types.head_norm d t in
    match t'.Types.t with
      | Types.Ttup ts ->
        let shs = List.map (lean_size_shape d siblings) ts in
        if List.for_all (fun sh -> sh = CSleaf) shs then CSleaf else CStuple shs
      | Types.Tapp (ts, p) ->
        (match List.find_opt (fun (q, _) -> Path.compare p q = 0) siblings with
          | Some (_, name) -> CSsibling name
          | None ->
            (match Name.to_string (Path.get_name p), ts with
              | "list", [e] ->
                (match lean_size_shape d siblings e with CSleaf -> CSleaf | sh -> CSlist (e, sh))
              | "maybe", [e] ->
                (match lean_size_shape d siblings e with CSleaf -> CSleaf | sh -> CSoption (e, sh))
              | "either", [l; r] ->
                let shl = lean_size_shape d siblings l and shr = lean_size_shape d siblings r in
                if shl = CSleaf && shr = CSleaf then CSleaf else CSsum ((l, shl), (r, shr))
              | _ -> CSleaf))
      | _ -> CSleaf

(* One block's size analysis, shared by the census and the emission.
   Returns None when the block gets no size functions (with the reason),
   or Some members: (path, Lean type name, tnvar_list, ctors) with ctor =
   (Lean constructor name, field types). *)
let lean_size_block (env : env) (module_name : string)
    (ts_list : (name_l * Typed_ast.tnvar list * Path.t * texp * name_sect option) list)
  : ((Path.t * string * Typed_ast.tnvar list * (string * Types.t list) list) list, string) result =
  let target = Target.Target_no_ident Target.Target_lean in
  let l = Ast.Trans (false, "lean_size_block", None) in
  let non_abbrev = List.filter (fun (_, _, _, t, _) -> match t with Te_abbrev _ -> false | _ -> true) ts_list in
  if is_library_module module_name then Error "a library type (sizes are derived for user modules only)"
  else if non_abbrev = [] then Error "a type abbreviation"
  else begin
    let param_counts = List.map (fun (_, tvs, _, _, _) -> List.length tvs) non_abbrev in
    let is_type1 = match param_counts with
      | [] -> false | x :: xs -> not (List.for_all (fun y -> y = x) xs) in
    if is_type1 then Error "a member of a heterogeneous (indexed, Type 1) mutual block"
    else begin
      let member ((_, _), tnvar_list, path, t, _) =
        let td = Types.type_defs_lookup l env.t_env path in
        if Target.Targetmap.apply_target td.Types.type_target_rep target <> None then
          Error "a type with a Lean target_rep (rendered as an abbrev of a hand-written type)"
        else
          let name = Name.to_string (Typed_ast_syntax.type_descr_to_name target path td) in
          match t with
            | Te_opaque -> Error "an opaque type (no constructors)"
            | Te_variant (_, ctors) ->
              let ctors = List.map (fun ((_, _), c_ref, _, args) ->
                  let cd = c_env_lookup l env.c_env c_ref in
                  let (_, cname, _) = Typed_ast_syntax.constant_descr_to_name target cd in
                  (Name.to_string cname, List.map (fun (s : src_t) -> s.typ) (Seplist.to_list args)))
                (Seplist.to_list ctors) in
              Ok (path, name, tnvar_list, ctors)
            | Te_record (_, _, fields, _) ->
              Ok (path, name, tnvar_list, [("mk", List.map (fun (_, _, _, (s : src_t)) -> s.typ) (Seplist.to_list fields))])
            | Te_abbrev _ -> Error "a type abbreviation" in
      let rec collect acc = function
        | [] -> Ok (List.rev acc)
        | td :: rest -> (match member td with Ok m -> collect (m :: acc) rest | Error e -> Error e) in
      match collect [] non_abbrev with
        | Error e -> Error e
        | Ok members ->
          let siblings = List.map (fun (p, nm, _, _) -> (p, nm)) members in
          let paths = List.map fst siblings in
          let fields = List.concat_map (fun (_, _, _, ctors) -> List.concat_map snd ctors) members in
          let recursive = List.exists (fun ty -> lean_size_shape env.t_env siblings ty <> CSleaf) fields in
          (* A block whose only sibling references
             sit under heads the derivation cannot count (`set t`, a user
             type applied to `t`) IS recursive — say so, and say why no size
             is derived, instead of calling it non-recursive *)
          let refs_sibling = List.exists (lean_typ_refs_paths env.t_env paths) fields in
          if recursive then Ok members
          else if refs_sibling then
            Error "a type recursive ONLY through an unsupported container head (a `set`, a `map`, a user type applied to the recursive type, a function type — the derivation counts siblings only through tuples, `list`, `maybe` and `either`), so no derived size bounds its recursion; write a hand-written computable size in a Lean module the generated module imports (`declare {lean} extra_import`) and name it qualified in the measure"
          else
            Error "a non-recursive type (its size is the constant 1 — a measure over it would be a magic value; measure the data that actually decreases)" 
    end
  end

(* Census pre-pass over one module's type blocks (recursing into lem
   submodules, whose names prefix the Lean type name). Runs for every
   typechecked module (lean_analysis_prepass_all) and again per emitted
   module (lean_defs); insertions are idempotent. *)
let lean_size_prepass env (ds : def list) =
  let rec walk (ns : string list) (((d_aux, _), _, _) : def) =
    match d_aux with
      (* A type with a Lean target_rep reaches the
         backend as a Comment-wrapped Type_def (the target's def_trans
         comments it out; the emitter renders the abbrev from the Comment
         case) — walk into it so the census carries the target_rep reason
         instead of "not a generated inductive type of this invocation" *)
      | Comment c -> walk ns c
      | Module (_, (name, _), _, _, _, inner, _) ->
        let n = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name)) in
        List.iter (walk (ns @ [n])) inner
      | Type_def (_, defs) ->
        let ts_list = Seplist.to_list defs in
        let register p st =
          if size_census_lookup p = None then St.size_census := (p, st) :: !St.size_census in
        (match lean_size_block env !St.current_module_name ts_list with
          | Ok members ->
            List.iter (fun (p, nm, _, _) ->
                register p (Size_fn (String.concat "." (ns @ [nm])))) members
          | Error reason ->
            List.iter (fun (_, _, p, t, _) ->
                match t with Te_abbrev _ -> () | _ -> register p (Size_none reason)) ts_list)
      | _ -> () in
  List.iter (walk []) ds

let lean_thread_lookup (c : Types.const_descr_ref) : (int list * string list) option =
  Types.Cdmap.apply !St.failwith_threaded c
(* LEM_THREAD_DEBUG set: trace the [Inhabited] threading fixpoint on stderr
   (DESIGN, "Debugging the analyses"). *)
let lean_thread_debug = Sys.getenv_opt "LEM_THREAD_DEBUG" <> None

(* ===== The reserved-name CAPTURE check =====

   The reserved-binder scan (reserved_binder_check, emission) refuses a lem
   BINDER named like a synthesized binder. It does not see what a
   referenced CONSTANT renders as: a constant whose Lean target_rep text is
   `lemTail` (or `lemFuel`) renders as exactly that identifier inside the
   worker, where the synthesized binder is in scope — captured silently.
   Measured: `declare lean target_rep function dl = `lemTail`` referenced
   in a hoisted body evaluated 4 on Lean vs 1 on OCaml; the same shape
   with `lemFuel` was accepted too. One generic check for every
   reserved name: every constant the clause body references contributes
   the identifiers of its Lean rep (`CR_simple`/`CR_inline` bodies —
   every `Backend` ident in the rep expression —, `CR_infix`'s ident,
   `CR_special_rep`'s text) and its lem name (the rendered name of a
   constant without a rep, modulo the collision renaming, which never
   produces a reserved word); plus every `Backend` ident written directly
   in the body (an already-inlined rep). Any of them equal to a reserved
   name, or carrying a reserved prefix, is refused with the constant and
   the text named. Run for every fuel'd/reader/supply group
   (reserved_binder_check) and whenever a `function` tail is hoisted
   (lean_hoist_tail_binders). *)
let lean_starts_with (pre : string) (s : string) : bool =
  String.length s >= String.length pre && String.sub s 0 (String.length pre) = pre

(* THE RESERVED-NAME TABLE: every identifier the backend synthesizes into
   generated code, in one place, so the checks that read it cannot drift
   apart. The populations checked against it:
   - the BINDERS of a fuel'd/reader/supply definition — its parameters and
     every binder inside its clause bodies (reserved_binder_check): the
     binder names and the prefixes. `lemTail` is deliberately not a binder
     name: the tail hoisting synthesizes it into the very clause this check
     scans (lean_hoist_tail_binders runs first) and guards the user's
     binders against it itself;
   - the Lean names a referenced constant RENDERS as
     (lean_reserved_capture_check): every exact name and the prefixes;
   - top-level DEFINITION names: the synthesized destructuring-let family
     `lemLetRhs_*` (lean_check_reserved_def_name);
   - the free variables of a long if/else-if chain: its continuations
     `_lemIfTail<n>`; constructor and field names of a recursive type
     block: the derived size functions `lemSize`/`lemSize_aux<k>` in the
     type's namespace (generate_lem_size).
   The class name `LemFuel` is also avoided through library/lean_constants
   like every other root Lean name. *)
let lean_reserved_binder_names = ["lemFuel"; "lemMeasureLe"; "lemHyp"]
let lean_reserved_tail_name = "lemTail"       (* the hoisted `function` scrutinee *)
let lean_reserved_rec_base_name = "lemRecBase" (* the bound base of a mutual-record update *)
let lean_reserved_exact_names =
  lean_reserved_binder_names @ ["LemFuel"; lean_reserved_tail_name; lean_reserved_rec_base_name]
let lean_reserved_prefixes = ["_lemReader_"; "_lemSupply"]
let lean_reserved_let_rhs_prefix = "lemLetRhs_"
let lean_reserved_if_tail_prefix = "_lemIfTail"
let lean_reserved_size_name = "lemSize"
let lean_reserved_size_aux_prefix = "lemSize_aux"
let lean_has_reserved_prefix (n : string) : bool =
  List.exists (fun pre -> lean_starts_with pre n) lean_reserved_prefixes
let lean_is_reserved_binder (n : string) : bool =
  List.mem n lean_reserved_binder_names || lean_has_reserved_prefix n
let lean_is_reserved_name (n : string) : bool =
  List.mem n lean_reserved_exact_names || lean_has_reserved_prefix n
(* The reserved names as the error messages list them. *)
let lean_reserved_names_text (names : string list) : string =
  String.concat "" [
    String.concat ", " (List.map (Printf.sprintf "'%s'") names);
    " and the ";
    String.concat "/" (List.map (Printf.sprintf "'%s'") lean_reserved_prefixes);
    " prefixes"]

(* Instance priorities come from one table, the lattice note
   doc/notes/2026-08-22_arc14-instance-priority-lattice.md (with its
   2026-10-03 addendum): model-declared and derived BEq/Ord instances at
   Lean's default (1000); the automatic SetType/Eq0/Ord0 trio at the "auto"
   slot (500), so a model's own instance wins by priority and not by
   declaration order; core's `[DecidableEq a] : BEq a` is also at 500
   (Init/Prelude), so the two library bridges that make a `BEq` out of a Lem
   dictionary sit BELOW it — `[Eq0 a] : BEq a` at 450 and the
   comparator-derived `[SetType a]`/`[MapKeyType a] : BEq a` at 400 ([USER
   2026-10-03] "(a) 450/400"): `==` at a base type is core's structural
   equality, with `LawfulBEq` and the core simp set, and where no core
   instance exists the Eq0 bridge still beats the comparator route, which can
   be coarser than the type's own equality; generic defaults and residual
   instances at `low` (100). *)
let lean_instance_auto_priority = 500
let lean_instance_eq0_bridge_priority = 450
let lean_instance_comparator_bridge_priority = 400
let lean_instance_kw (priority : int) =
  Printf.sprintf "\ninstance (priority := %d)" priority
let lean_instance_kw_auto = lean_instance_kw lean_instance_auto_priority

(* every `Backend` identifier (a target_rep's Lean text) in an expression *)
let rec exp_backend_idents (e : exp) : string list =
  let seplist_exps sl = Seplist.to_list sl in
  match ExpW.exp_to_term e with
  | Backend (_, i) -> [String.trim (Ident.to_string i)]
  | Var _ | Nvar_e _ | Constant _ | Lit _ -> []
  | Fun (_, _, _, e1) -> exp_backend_idents e1
  | Function (_, arms, _) ->
    List.concat_map (fun (_, _, e1, _) -> exp_backend_idents e1) (Seplist.to_list arms)
  | App (e1, e2) -> exp_backend_idents e1 @ exp_backend_idents e2
  | Infix (e1, e2, e3) ->
    exp_backend_idents e1 @ exp_backend_idents e2 @ exp_backend_idents e3
  | Record (_, fes, _) ->
    List.concat_map (fun (_, _, e1, _) -> exp_backend_idents e1) (Seplist.to_list fes)
  | Recup (_, e0, _, fes, _) ->
    exp_backend_idents e0
    @ List.concat_map (fun (_, _, e1, _) -> exp_backend_idents e1) (Seplist.to_list fes)
  | Field (e1, _, _) -> exp_backend_idents e1
  | Vector (_, es, _) | Tup (_, es, _) | List (_, es, _) | Set (_, es, _) ->
    List.concat_map exp_backend_idents (seplist_exps es)
  | VectorSub (e1, _, _, _, _, _) | VectorAcc (e1, _, _, _) -> exp_backend_idents e1
  | Case (_, _, e0, _, arms, _) ->
    exp_backend_idents e0
    @ List.concat_map (fun (_, _, e1, _) -> exp_backend_idents e1) (Seplist.to_list arms)
  | Typed (_, e1, _, _, _) | Paren (_, e1, _) | Begin (_, e1, _) -> exp_backend_idents e1
  | Let (_, (lb, _), _, body) ->
    (match lb with
     | Let_val (_, _, _, rhs) -> exp_backend_idents rhs
     | Let_fun (_, _, _, _, rhs) -> exp_backend_idents rhs) @ exp_backend_idents body
  | If (_, e1, _, e2, _, e3) ->
    exp_backend_idents e1 @ exp_backend_idents e2 @ exp_backend_idents e3
  | Setcomp (_, e1, _, e2, _, _) -> exp_backend_idents e1 @ exp_backend_idents e2
  | Comp_binding (_, _, e1, _, _, _, _, e2, _) -> exp_backend_idents e1 @ exp_backend_idents e2
  | Quant (_, _, _, e1) -> exp_backend_idents e1
  | Do (_, _, dls, _, e1, _, _) ->
    List.concat_map (fun (Do_line (_, _, rhs, _)) -> exp_backend_idents rhs) dls
    @ exp_backend_idents e1

(* ===== Comparison-dictionary threading =====
   Lem's DEFAULT instances of Eq and SetType (and MapKeyType, via SetType)
   are OCaml's polymorphic comparison: available at every type, no
   dictionary. The Lean realisation of such a comparison at a type
   mentioning a type variable `a` of the enclosing definition is the
   bounded structural instance of that type, which needs Lean `[Ord a]` (or
   `[BEq a]` for Eq). This pre-pass computes, per definition, which such
   binders its body demands:
   - every use of a constant whose Lem class constraint (Eq / SetType /
     MapKeyType / Ord) is instantiated at a type containing `a` demands
     `[BEq a]` (Eq) or `[Ord a]` (the others) -- except when the type IS
     `a` and the definition itself carries that Lem constraint on `a`
     (the dictionary is then in scope);
   - every use of a generated definition that received such binders
     demands them at the instantiated types (transitively; fixpoint).
   The binders are emitted after the definition's Lem constraints
   (val_def). There is no fallback: a demand this analysis misses is a Lean
   compile error, never the retired runtime-panicking residual instance.
   The demand table is St.lean_cmp_bounds. *)

let rec exp_constants (e : exp) : const_descr_ref id list =
  let seplist_exps sl = Seplist.to_list sl in
  match ExpW.exp_to_term e with
  | Constant c -> [c]
  | Backend _ | Var _ | Nvar_e _ | Lit _ -> []
  | Fun (_, _, _, e1) -> exp_constants e1
  | Function (_, arms, _) ->
    List.concat_map (fun (_, _, e1, _) -> exp_constants e1) (Seplist.to_list arms)
  | App (e1, e2) -> exp_constants e1 @ exp_constants e2
  | Infix (e1, e2, e3) -> exp_constants e1 @ exp_constants e2 @ exp_constants e3
  | Record (_, fes, _) ->
    List.concat_map (fun (_, _, e1, _) -> exp_constants e1) (Seplist.to_list fes)
  | Recup (_, e0, _, fes, _) ->
    exp_constants e0 @ List.concat_map (fun (_, _, e1, _) -> exp_constants e1) (Seplist.to_list fes)
  | Field (e1, _, _) -> exp_constants e1
  | Vector (_, es, _) | Tup (_, es, _) | List (_, es, _) | Set (_, es, _) ->
    List.concat_map exp_constants (seplist_exps es)
  | VectorSub (e1, _, _, _, _, _) | VectorAcc (e1, _, _, _) -> exp_constants e1
  | Case (_, _, e0, _, arms, _) ->
    exp_constants e0 @ List.concat_map (fun (_, _, e1, _) -> exp_constants e1) (Seplist.to_list arms)
  | Typed (_, e1, _, _, _) | Paren (_, e1, _) | Begin (_, e1, _) -> exp_constants e1
  | Let (_, (lb, _), _, body) ->
    (match lb with
     | Let_val (_, _, _, rhs) -> exp_constants rhs
     | Let_fun (_, _, _, _, rhs) -> exp_constants rhs) @ exp_constants body
  | If (_, e1, _, e2, _, e3) -> exp_constants e1 @ exp_constants e2 @ exp_constants e3
  | Setcomp (_, e1, _, e2, _, _) -> exp_constants e1 @ exp_constants e2
  | Comp_binding (_, _, e1, _, _, _, _, e2, _) -> exp_constants e1 @ exp_constants e2
  | Quant (_, _, _, e1) -> exp_constants e1
  | Do (_, _, dls, _, e1, _, _) ->
    List.concat_map (fun (Do_line (_, _, rhs, _)) -> exp_constants rhs) dls @ exp_constants e1

let lean_cmp_class_of_lem (p : Path.t) : string option =
  match Name.to_string (Path.get_name p) with
  | "Eq" -> Some "BEq"
  | "SetType" | "MapKeyType" | "Ord" -> Some "Ord"
  | _ -> None

let tnvar_name (tv : Types.tnvar) : string = Ulib.Text.to_string (Types.tnvar_to_rope tv)

(* ---- Type-variable capture
   A value definition's type variables are Lean implicit binders
   (`{a : Type}`), which shadow every global of that name in the
   definition's signature and body: `type t = …` with
   `let f (x : 't) (y : t)` made `(y : t)` refer to the binder, and
   `let a : nat = 3` with `let f (x : 'a) : nat = a` made `a` the Type.
   Lem already renames a PARAMETER that collides with a type variable (the
   local `a` of p_tyvar_shadow becomes `a1`); the backend does the same for
   the type variable. Every name the definition refers to is collected —
   the Lean name of each constant it mentions, and the Lean name (plus the
   components of a Lean target representation) of each type constructor in
   the type of any sub-expression or pattern — and a type variable equal to
   one of them is rendered under a fresh name (`t'`, `t''`, …) that is none
   of those names, none of the definition's other type variables, none of
   its binders and not reserved. The primed shape is deliberate: Lem's own
   renamer (default_avoid_f, Name.fresh) renames a colliding local binder
   to `t1`, `t2`, … at render time, after this map is computed, so a
   digit-suffixed fresh name here could meet a renamed binder (measured:
   `let t = tn y` in the body became `t1`); the renamer never produces a
   prime. The map is [render]-scoped
   (St.tyvar_renames) and consulted by every renderer of a type variable
   reached from a value definition: the implicit binders
   (let_type_variables), the two source-type renderers (pat_typ, typ), the
   class-constraint and comparison-dictionary binders (val_def). Numeric
   type variables are not renamed (no collision shape is known). Type
   DEFINITIONS are not renamed: a type parameter's name is part of the
   generated API (`inductive t (a : Type)`, named arguments), so a
   collision there is refused instead (lean_check_type_block). *)
let lean_tyvar_text (s : string) : string =
  match List.assoc_opt s !St.tyvar_renames with Some s' -> s' | None -> s

(* every type-constructor path in a type; the flag marks a Tbackend path,
   whose components are the Lean text itself *)
let rec lean_typ_type_paths (ty : Types.t) : (Path.t * bool) list =
  match ty.Types.t with
  | Types.Tvar _ | Types.Tne _ | Types.Tuvar _ -> []
  | Types.Tfn (t1, t2) -> lean_typ_type_paths t1 @ lean_typ_type_paths t2
  | Types.Ttup ts -> List.concat_map lean_typ_type_paths ts
  | Types.Tapp (ts, p) -> (p, false) :: List.concat_map lean_typ_type_paths ts
  | Types.Tbackend (ts, p) -> (p, true) :: List.concat_map lean_typ_type_paths ts

let rec lean_src_t_type_paths (t : src_t) : (Path.t * bool) list =
  match t.term with
  | Typ_wild _ | Typ_var _ | Typ_len _ -> []
  | Typ_fn (t1, _, t2) -> lean_src_t_type_paths t1 @ lean_src_t_type_paths t2
  | Typ_tup ts -> List.concat_map lean_src_t_type_paths (Seplist.to_list ts)
  | Typ_app (p, ts) -> (p.descr, false) :: List.concat_map lean_src_t_type_paths ts
  | Typ_backend (p, ts) -> (p.descr, true) :: List.concat_map lean_src_t_type_paths ts
  | Typ_paren (_, t1, _) | Typ_with_sort (t1, _) -> lean_src_t_type_paths t1

(* the type of every pattern node / expression node (the renderers print
   parameter and binder types from these) *)
let rec lean_types_of_pat (p : pat) : Types.t list =
  p.typ :: (match p.term with
    | P_wild _ | P_var _ | P_lit _ | P_var_annot _ | P_num_add _ -> []
    | P_as (_, p', _, _, _) | P_typ (_, p', _, _, _) | P_paren (_, p', _) -> lean_types_of_pat p'
    | P_tup (_, ps, _) | P_list (_, ps, _) | P_vector (_, ps, _) ->
      List.concat_map lean_types_of_pat (Seplist.to_list ps)
    | P_vectorC (_, ps, _) | P_const (_, ps) | P_backend (_, _, _, ps) -> List.concat_map lean_types_of_pat ps
    | P_record (_, fps, _) -> List.concat_map (fun (_, _, p') -> lean_types_of_pat p') (Seplist.to_list fps)
    | P_cons (p1, _, p2) -> lean_types_of_pat p1 @ lean_types_of_pat p2)

let rec lean_types_of_exp (e : exp) : Types.t list =
  let sub = lean_types_of_exp in
  let pats ps = List.concat_map lean_types_of_pat ps in
  let qbs_types qbs = List.concat_map (function
      | Qb_var _ -> []
      | Qb_restr (_, _, p, _, e1, _) -> lean_types_of_pat p @ sub e1) qbs in
  Typed_ast.exp_to_typ e :: (match ExpW.exp_to_term e with
  | Var _ | Nvar_e _ | Constant _ | Backend _ | Lit _ -> []
  | Fun (_, ps, _, e1) -> pats ps @ sub e1
  | Function (_, arms, _) ->
    List.concat_map (fun (p, _, e1, _) -> lean_types_of_pat p @ sub e1) (Seplist.to_list arms)
  | App (e1, e2) -> sub e1 @ sub e2
  | Infix (e1, e2, e3) -> sub e1 @ sub e2 @ sub e3
  | Record (_, fes, _) -> List.concat_map (fun (_, _, e1, _) -> sub e1) (Seplist.to_list fes)
  | Recup (_, e0, _, fes, _) -> sub e0 @ List.concat_map (fun (_, _, e1, _) -> sub e1) (Seplist.to_list fes)
  | Field (e1, _, _) -> sub e1
  | Vector (_, es, _) | Tup (_, es, _) | List (_, es, _) | Set (_, es, _) ->
    List.concat_map sub (Seplist.to_list es)
  | VectorSub (e1, _, _, _, _, _) | VectorAcc (e1, _, _, _) -> sub e1
  | Case (_, _, e0, _, arms, _) ->
    sub e0 @ List.concat_map (fun (p, _, e1, _) -> lean_types_of_pat p @ sub e1) (Seplist.to_list arms)
  | Typed (_, e1, _, _, _) | Paren (_, e1, _) | Begin (_, e1, _) -> sub e1
  | Let (_, (lb, _), _, body) ->
    (match lb with
     | Let_val (p, _, _, rhs) -> lean_types_of_pat p @ sub rhs
     | Let_fun (_, ps, _, _, rhs) -> pats ps @ sub rhs) @ sub body
  | If (_, e1, _, e2, _, e3) -> sub e1 @ sub e2 @ sub e3
  | Setcomp (_, e1, _, e2, _, _) -> sub e1 @ sub e2
  | Comp_binding (_, _, e1, _, _, qbs, _, e2, _) -> sub e1 @ qbs_types qbs @ sub e2
  | Quant (_, qbs, _, e1) -> qbs_types qbs @ sub e1
  | Do (_, _, dls, _, e1, _, _) ->
    List.concat_map (fun (Do_line (p, _, rhs, _)) -> lean_types_of_pat p @ sub rhs) dls @ sub e1)


(* Lem's polymorphic-comparison PRIMITIVES (library basic_classes.lem): no
   class constraint in Lem (they ARE OCaml's polymorphic compare), but their
   Lean reps (`==`, `defaultCompare`, ...) need the Lean class at the type
   they are used at. The default Eq instance's method inlines to
   unsafe_structural_equality, so `x = y` at an unconstrained parameterized
   type reaches the backend as one of these. *)
let lean_cmp_primitive (cd : const_descr) : string option =
  match Path.to_name_list cd.const_binding with
  | (mods, n) when List.exists (fun m -> Name.to_string m = "Basic_classes") mods ->
    (match Name.to_string n with
     | "unsafe_structural_equality" | "unsafe_structural_inequality" -> Some "BEq"
     | "defaultCompare" | "defaultLess" | "defaultLessEq" | "defaultGreater" | "defaultGreaterEq" -> Some "Ord"
     | _ -> None)
  | _ -> None

let lean_cmp_prepass env (ds : def list) =
  let l = Ast.Trans (false, "lean_cmp_prepass", None) in
  let val_def_bodies (vd : val_def) : exp list =
    match vd with
    | Let_def (_, _, (_, _, _, _, e)) -> [e]
    | Fun_def (_, _, _, funs) -> Seplist.to_list_map (fun ((_, _, _, _, _, e) : funcl_aux) -> e) funs
    | Let_inline _ -> [] in
  let rec collect acc (((d_aux, _), _, _) : def) =
    match d_aux with
    | Module (_, _, _, _, _, inner, _) -> List.fold_left collect acc inner
    | Val_def vd -> vd :: acc
    | _ -> acc in
  let vds = List.rev (List.fold_left collect [] ds) in
  let demands_of (vd : val_def) : (string * string) list =
    let tvs = List.filter_map (fun tv -> match tv with Types.Ty _ -> Some (tnvar_name tv) | Types.Nv _ -> None)
      (Types.TNset.elements (val_def_get_free_tnvars env vd)) in
    let explicit = List.map (fun (p, tv) -> (Name.to_string (Path.get_name p), tnvar_name tv))
      (val_def_get_class_constraints env vd) in
    let out = ref [] in
    let add cls a = if List.mem a tvs && not (List.mem (cls, a) !out) then out := (cls, a) :: !out in
    List.iter (fun e ->
      List.iter (fun (c : const_descr_ref id) ->
        let cd = c_env_lookup l env.c_env c.descr in
        let inst_of tv =
          let rec go ps is = match ps, is with
            | p :: ps', i :: is' -> if Types.tnvar_compare p tv = 0 then Some i else go ps' is'
            | _ -> None in
          go cd.const_tparams c.instantiation in
        (* Lean class demanded when Lem resolves class [lem_p] at [ty]:
           follow Lem's instance resolution; an explicit instance (tuples,
           list, maybe, ...) passes the demand to its own constraints; the
           DEFAULT instance (polymorphic compare) is realised by bounded
           structural instances, which need the Lean class on every type
           variable below. *)
        let rec lem_demand depth (lem_p : Path.t) (ty : Types.t) =
          match lean_cmp_class_of_lem lem_p with
          | None -> ()
          | Some cls ->
            let lem_cls = Name.to_string (Path.get_name lem_p) in
            (match ty.Types.t with
             | Types.Tvar _ ->
               let a = (match Types.TNset.elements (Types.free_vars ty) with v :: _ -> tnvar_name v | [] -> "") in
               if not (List.mem (lem_cls, a) explicit) then add cls a
             | _ when Types.TNset.is_empty (Types.free_vars ty) -> ()
             | _ ->
               let default_all () =
                 List.iter (fun fv -> add cls (tnvar_name fv)) (Types.TNset.elements (Types.free_vars ty)) in
               (* Depth bound, loud like its twin in lean_tuple_inst_demands
                  (it used to fall back to default_all, which silently
                  over-approximates the binders and so changes a
                  declaration's type). A bound, not a proof: no chain near it
                  is known. *)
               if depth > 50 then
                 raise (Reporting_basic.err_general true c.id_locn
                   (Stdlib.(^) "Lean backend: internal error — comparison-binder demand walk exceeded depth 50 at class "
                      (Path.to_string lem_p)));
               (match Types.get_matching_instance env.t_env (lem_p, ty) env.i_env with
                | Some (inst, subst) when not inst.Types.inst_is_default ->
                  List.iter (fun (p', tv') ->
                    match Types.TNfmap.apply subst tv' with
                    | Some ty' -> lem_demand (depth + 1) p' ty'
                    | None -> ()) inst.Types.inst_constraints
                | _ -> default_all ())) in
        let demand ~lem_p cls tv =
          match inst_of tv with
          | None -> ()
          | Some ty ->
            (match lem_p with
             | Some p -> lem_demand 0 p ty
             | None ->
               (* a threaded Lean-class binder of a generated callee: the Lean
                  instance at [ty] needs the class on its type variables *)
               List.iter (fun fv -> add cls (tnvar_name fv)) (Types.TNset.elements (Types.free_vars ty))) in
        List.iter (fun (p, tv) ->
          match lean_cmp_class_of_lem p with
          | Some cls -> demand ~lem_p:(Some p) cls tv
          | None -> ()) cd.const_class;
        (match lean_cmp_primitive cd, cd.const_tparams with
         | Some cls, tv :: _ -> demand ~lem_p:None cls tv
         | _ -> ());
        (match Hashtbl.find_opt St.lean_cmp_bounds c.descr with
         | Some bs ->
           List.iter (fun (cls, tvn) ->
             List.iter (fun tv -> if tnvar_name tv = tvn then demand ~lem_p:None cls tv) cd.const_tparams) bs
         | None -> ())) (exp_constants e)) (val_def_bodies vd);
    (* declaration order of the definition's type variables, then class *)
    List.concat_map (fun a -> List.filter (fun (_, b) -> b = a) (List.rev !out)) tvs in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun vd ->
      let ds' = demands_of vd in
      List.iter (fun c ->
        let old = Option.value ~default:[] (Hashtbl.find_opt St.lean_cmp_bounds c) in
        let merged = List.fold_left (fun acc x -> if List.mem x acc then acc else acc @ [x]) old ds' in
        if List.length merged <> List.length old then begin
          Hashtbl.replace St.lean_cmp_bounds c merged; changed := true end)
        (match vd with
         | Let_def(_, _, (_, nm, _, _, _)) -> List.map snd nm
         | Let_inline(_,_,_,_,c,_,_,_) -> [c]
         | Fun_def(_, _, _, funs) ->
           Seplist.to_list_map (fun ((_, c, _, _, _, _):funcl_aux) -> c) funs)) vds
  done

(* ===== Tuple instances of different arities =====
   Lem tuples are n-ary; Lean's are right-nested pairs, so the Lean type of
   a Lem triple whose LAST component is a pair, `a × b × (c × d)`, IS the
   Lean type of a quadruple. A class with instances at several tuple
   arities (linksem's Show: pair, triple, quad) therefore has overlapping
   Lean instances at such a type, and Lean picks the most recently
   declared one (the quad: `(x, y, (z, w))` showed as "(x, y, z, w)"),
   where Lem's resolution picks the triple. The backend resolves such
   demands the Lem way: tuple instances get a global name
   (lean_tuple_inst_name), and a use of a constant whose class constraints
   reach a confusable tuple type binds exactly Lem's instance locally,
   innermost first (`haveI := lemInst_... T1 T2 T3; e`); Lean's local
   instances take precedence over global ones.
   Exempt: Basic_classes' Eq / Ord / SetType / MapKeyType. Their tuple
   instances are componentwise / lexicographic, so the overlapping choice
   computes the same result; binding them would only add noise. *)
let lean_tuple_inst_exempt (cls : Path.t) : bool =
  let (mods, n) = Path.to_name_list cls in
  List.exists (fun m -> Name.to_string m = "Basic_classes") mods
  && List.mem (Name.to_string n) ["Eq"; "Ord"; "SetType"; "MapKeyType"]

(* The global Lean name of a non-default tuple instance: from Lem's instance
   path (module path + Instance_<class>_<type>), with `Lem_` for library
   modules (a user module may share a library module's name: linksem's
   Show and LemLib's Show both have a pair instance of their Show). *)
let lean_tuple_inst_name env (inst : Types.instance) : string =
  let l = Ast.Trans (false, "lean_tuple_inst_name", None) in
  let (mods, n) = Path.to_name_list inst.Types.inst_binding in
  let is_lib = match mods with
    | m :: _ ->
      (match Types.Pfmap.apply env.e_env (Path.mk_path [] m) with
       | Some md -> Backend_common.lean_module_is_library md
       | None ->
         raise (Reporting_basic.err_general true l
           (Stdlib.(^) "Lean backend: internal error — module of instance not found: "
              (Path.to_string inst.Types.inst_binding))))
    | [] ->
      raise (Reporting_basic.err_general true l
        "Lean backend: internal error — instance path without a module") in
  String.concat "" [ "lemInst_"; (if is_lib then "Lem_" else "");
                     String.concat "_" (List.map Name.to_string (mods @ [n])) ]

let lean_tuple_inst_named env (inst : Types.instance) : bool =
  not inst.Types.inst_is_default
  && not (lean_tuple_inst_exempt inst.Types.inst_class)
  && (match (Types.head_norm env.t_env inst.Types.inst_type).Types.t with
      | Types.Ttup _ -> true | _ -> false)

(* A Lem tuple type that a longer Lean tuple type also matches. *)
let lean_tuple_confusable env (ty : Types.t) : bool =
  match (Types.head_norm env.t_env ty).Types.t with
  | Types.Ttup ts ->
    (match List.rev ts with
     | last :: _ :: _ ->
       (match (Types.head_norm env.t_env last).Types.t with Types.Ttup _ -> true | _ -> false)
     | _ -> false)
  | _ -> false

(* The confusable tuple-instance demands of one constant use, innermost
   first, deduplicated: (instance, type-variable substitution, type). *)
let lean_tuple_inst_demands env (c : const_descr_ref id)
    : (Types.instance * Types.t Types.TNfmap.t * Types.t) list =
  let l = Ast.Trans (false, "lean_tuple_inst_demands", None) in
  let cd = c_env_lookup l env.c_env c.descr in
  let out = ref [] in
  let rec walk depth (p : Path.t) (ty : Types.t) =
    (* Depth bound. It used to be a silent cut-off (demands past it left
       unbound); now exceeding it is a loud refusal (fail-closed). It is a
       bound, not a proof: a legitimate constraint chain deeper than 50
       would also be refused (loudly). Lem's instance constraints are
       normally on component types, so real chains are short; no case
       near the bound is known. *)
    if depth > 50 then
      raise (Reporting_basic.err_general true c.id_locn
        (Stdlib.(^) "Lean backend: internal error — the tuple-instance walk exceeded depth 50 at class "
           (Path.to_string p)));
    if not (lean_tuple_inst_exempt p) then
      match Types.get_matching_instance env.t_env (p, ty) env.i_env with
      | Some (inst, subst) when not inst.Types.inst_is_default ->
        List.iter (fun (p', tv') ->
          match Types.TNfmap.apply subst tv' with
          | Some ty' -> walk (depth + 1) p' ty'
          | None -> ()) inst.Types.inst_constraints;
        if lean_tuple_confusable env ty then begin
          if not (lean_tuple_inst_named env inst) then
            raise (Reporting_basic.err_general true l
              (Stdlib.(^) "Lean backend: internal error — confusable tuple instance is not named: "
                 (Path.to_string inst.Types.inst_binding)));
          if not (List.exists (fun (i, _, t) ->
                    Path.compare i.Types.inst_binding inst.Types.inst_binding = 0
                    && Types.compare t ty = 0) !out)
          then out := !out @ [(inst, subst, ty)]
        end
      | _ -> () in
  let rec zip ps is = match ps, is with
    | p :: ps', i :: is' -> (p, i) :: zip ps' is'
    | _ -> [] in
  let inst_of = zip cd.const_tparams c.instantiation in
  List.iter (fun (p, tv) ->
    match List.find_opt (fun (tv', _) -> Types.tnvar_compare tv tv' = 0) inst_of with
    | Some (_, ty) -> walk 0 p ty
    | None -> ()) cd.const_class;
  !out

(* The constant heading an expression node (constant, application spine,
   infix operator): the node that receives the local tuple-instance bindings. *)
let lean_exp_head_const (e : exp) : const_descr_ref id option =
  let rec head e = match ExpW.exp_to_term e with
    | Constant c -> Some c
    | App (e1, _) -> head e1
    | _ -> None in
  match ExpW.exp_to_term e with
  | Constant c -> Some c
  | App _ -> head e
  | Infix (_, op, _) -> (match ExpW.exp_to_term op with Constant c -> Some c | _ -> None)
  | _ -> None

(* ===== Sequencing `let _ = e1 in e2` =====
   Lem's idiom for evaluating e1 for its effect (OCaml is strict: e1 runs,
   and a failure in e1 stops the program). Lean's compiler drops an unused
   pure let, and any Unit-typed value is interchangeable with `()`, so
   `let _ := e1; e2` / `match e1 with | () => e2` skipped e1 entirely: the
   model's diagnostics (`errln`) vanished and a failing e1 was not raised.
   Emitted as `lemSeq (fun _ => e1) (fun _ => e2)`: logically `e2`, at run
   time LemLib forces e1 first. Patterns: `_` and `()`; also the one-arm
   match Lem makes of `let () = e1 in e2`. *)
(* e1 that cannot have an effect or fail (a variable, a literal): the plain
   emission is kept. *)
let rec lean_seq_trivial (e : exp) : bool =
  match ExpW.exp_to_term e with
  | Var _ | Lit _ -> true
  | Paren (_, e1, _) | Typed (_, e1, _, _, _) | Begin (_, e1, _) -> lean_seq_trivial e1
  | _ -> false


(* B15b: a binding pattern that cannot fail to match (variables, wildcards,
   tuples of them): `let x = e1 in e2` with none of its variables used in e2
   is the same sequencing as `let _ = e1 in e2`. *)
let rec lean_seq_irrefutable (p : pat) : bool =
  match p.term with
  | P_wild _ | P_var _ | P_var_annot _ -> true
  | P_tup (_, ps, _) -> Seplist.for_all lean_seq_irrefutable ps
  | P_paren (_, p', _) | P_typ (_, p', _, _, _) -> lean_seq_irrefutable p'
  | _ -> false

let lean_seq_unused_binding (p : pat) (body : exp) : bool =
  lean_seq_irrefutable p
  && (let free = ExpW.exp_to_free body in
      NameSet.for_all (fun n -> not (Nfmap.in_dom n free)) (Typed_ast.pat_to_bound_names p))

let rec lean_seq_pattern (p : pat) : bool =
  match p.term with
  | P_wild _ -> true
  | P_lit { term = L_unit _ } -> true
  | P_paren (_, p', _) | P_typ (_, p', _, _, _) -> lean_seq_pattern p'
  | _ -> false

(* A bare `sorry` target representation is a proof
   hole, not a runtime boundary. Check declarations as well as uses, so
   an unused or partially applied constant cannot hide this escape.
   Raw Lean snippets remain trusted input, not a Lean parser/typechecker. *)
let lean_sorry_rep_error l name =
  Reporting_basic.err_general true l
    (Printf.sprintf
      "Lean backend: target representation `sorry` is forbidden (%s); provide a real Lean implementation, use failwithI for a declared runtime failure, or use a LemUnsupported. marker for an unsupported operation"
      name)

let lean_sorry_rep_check env =
  List.iter (fun cref ->
    let cd = c_env_lookup Ast.Unknown env.c_env cref in
    let names =
      match Target.Targetmap.apply_target cd.target_rep
              (Target.Target_no_ident Target_lean) with
      | Some (CR_simple (_, _, _, e)) | Some (CR_inline (_, _, _, e)) -> exp_backend_idents e
      | Some (CR_infix (_, _, _, i)) -> [String.trim (Ident.to_string i)]
      | Some (CR_special (_, _, CR_special_rep (strs, _), _)) -> List.map String.trim strs
      | _ -> [] in
    if List.mem "sorry" names then
      raise (lean_sorry_rep_error cd.spec_l (Path.to_string cd.const_binding)))
    (c_env_all_consts env.c_env);
  Types.Pfmap.fold (fun () path td ->
    match td with
    | Types.Tc_type d ->
      (match Target.Targetmap.apply_target d.Types.type_target_rep
               (Target.Target_no_ident Target_lean) with
       | Some (Types.TYR_simple (l, _, i)) when String.trim (Ident.to_string i) = "sorry" ->
         raise (lean_sorry_rep_error l (Path.to_string path))
       | _ -> ())
    | _ -> ()) () env.t_env

(* (what the constant renders as, the constant's lem name) for every
   constant an expression references, plus the body's own Backend idents *)
let lean_referenced_lean_names env (e : exp) : (string * string) list =
  let of_cref cref =
    let cd = c_env_lookup Ast.Unknown env.c_env cref in
    let lem_name = Name.to_string (Path.get_name cd.const_binding) in
    let reps = match Target.Targetmap.apply_target cd.target_rep (Target.Target_no_ident Target.Target_lean) with
      | Some (CR_simple (_, _, _, re)) | Some (CR_inline (_, _, _, re)) -> exp_backend_idents re
      | Some (CR_infix (_, _, _, i)) -> [String.trim (Ident.to_string i)]
      | Some (CR_special (_, _, CR_special_rep (strs, _), _)) -> List.map String.trim strs
      | Some (CR_special _) | Some (CR_undefined _) -> []
      | None -> [] in
    List.map (fun r -> (r, lem_name)) (lem_name :: reps) in
  List.concat_map of_cref (add_exp_entities empty_used_entities e).used_consts
  @ List.map (fun i -> (i, "(an inlined target_rep)")) (exp_backend_idents e)

let lean_reserved_capture_check env (l : Ast.l) (fname : string) (e : exp) : unit =
  List.iter (fun (rendered, lem_name) ->
      if lean_is_reserved_name rendered then
        raise (Reporting_basic.err_general true l
          (Printf.sprintf
            "Lean backend: the body of %s references constant %s, which renders on Lean as `%s` — a reserved synthesized binder name (the reserved-name contract: %s are the backend's); inside the generated code that identifier would be captured by the synthesized binder and compute a different value than the OCaml target — rename the constant or its Lean target_rep"
            fname lem_name rendered (lean_reserved_names_text lean_reserved_exact_names))))
    (lean_referenced_lean_names env e)

(* Constants whose LEAN target_rep is the bare identifier `failwith`
   (Assert_extra.failwith, cerberus's Utils.error, ...) — shared by the
   pre-pass and emission so the two can never disagree. *)
let lean_is_failwith_rep_env env cref =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  match Target.Targetmap.apply_target cd.target_rep (Target.Target_no_ident Target.Target_lean) with
  | Some (CR_simple (_, _, _, e)) | Some (CR_inline (_, _, _, e)) ->
    (match ExpW.exp_to_term e with
     | Backend (_, i) -> Ident.to_string i = "failwith"
     | _ -> false)
  | _ -> false

(* ===== Unsupported-construct hook ([USER 2026-09-03] exception class
   (c): a construct the Lean backend does
   not support may be REFUSED at generation time with a loud,
   construct-naming error — never emitted as something that computes a
   different result or silently drops).

   MECHANISM: a library `.lem` marks a constant or type as having NO Lean
   implementation by giving it a Lean target_rep whose identifier lives in
   the reserved `LemUnsupported.` namespace (library/num.lem: rational,
   real, float64, float32 and their value entry points; library/debug.lem:
   print_string, print_endline). Any reference to such a constant or type
   from a NON-library module is a generation-time error here. Library
   modules render the marker names (LemLib defines them, panicking, so the
   library's own instance code — `instance (Numeral rational) ...` —
   compiles); user code can never reach those instances without naming
   the type or an entry point, both refused. The marker is the whole
   protocol: adding a construct to the refused set is a one-line library
   change, no backend table. *)
let lean_unsupported_prefix = "LemUnsupported."
let lean_unsupported_ident_of_cref env cref : string option =
  let cd = c_env_lookup Ast.Unknown env.c_env cref in
  match Target.Targetmap.apply_target cd.target_rep (Target.Target_no_ident Target.Target_lean) with
  | Some (CR_simple (_, _, _, e)) | Some (CR_inline (_, _, _, e)) ->
    (match ExpW.exp_to_term e with
     | Backend (_, i) ->
       let s = String.trim (Ident.to_string i) in
       if String.length s > String.length lean_unsupported_prefix
          && String.sub s 0 (String.length lean_unsupported_prefix) = lean_unsupported_prefix
       then Some s else None
     | _ -> None)
  | _ -> None
let lean_unsupported_ident_of_type env (p : Path.t) : string option =
  match Types.type_defs_lookup_tc env.t_env p with
  | Some (Types.Tc_type td) ->
    (match Target.Targetmap.apply_target td.Types.type_target_rep (Target.Target_no_ident Target.Target_lean) with
     | Some (Types.TYR_simple (_, _, i)) ->
       let s = String.trim (Ident.to_string i) in
       if String.length s > String.length lean_unsupported_prefix
          && String.sub s 0 (String.length lean_unsupported_prefix) = lean_unsupported_prefix
       then Some s else None
     | _ -> None)
  | _ -> None
let lean_unsupported_check_cref env (l : Ast.l) cref : unit =
  if not (is_library_module !St.current_module_name) then
    match lean_unsupported_ident_of_cref env cref with
    | Some marker ->
      let cd = c_env_lookup Ast.Unknown env.c_env cref in
      raise (Reporting_basic.err_general true l
        (Printf.sprintf
          "Lean backend: constant '%s' has no implementation on the Lean target (its library rep is the unsupported marker '%s'; the OCaml reference implements it) — this use is REFUSED at generation time: remove it, or give the enclosing definition a Lean target_rep"
          (Path.to_string cd.const_binding) marker))
    | None -> ()
let lean_unsupported_check_type env (l : Ast.l) (p : Path.t) : unit =
  if not (is_library_module !St.current_module_name) then
    match lean_unsupported_ident_of_type env p with
    | Some marker ->
      raise (Reporting_basic.err_general true l
        (Printf.sprintf
          "Lean backend: type '%s' has no implementation on the Lean target (its library rep is the unsupported marker '%s'; the OCaml reference implements it) — this use is REFUSED at generation time"
          (Path.to_string p) marker))
    | None -> ()

let lean_typ_to_string (t : Types.t) : string =
  ignore (Format.flush_str_formatter ());
  Types.pp_type Format.str_formatter t;
  Format.flush_str_formatter ()

(* Collect, from one expression tree: failure SITES (the demanded
   Types.t of every failwith-rep application / bare reference and every
   L_undefined literal) and every constant REFERENCE with its type
   instantiation (for threading propagation). *)
type thread_scan = {
  mutable th_sites : (Types.t * Ast.l) list;
  mutable th_refs : (Types.const_descr_ref * Types.t list * Ast.l) list;
}

let lean_thread_scan_exp env (acc : thread_scan) (e : exp) : unit =
  let is_fw = lean_is_failwith_rep_env env in
  let sl_iter f sl = List.iter f (Seplist.to_list sl) in
  let rec go e =
    match ExpW.exp_to_term e with
    | App (e1, e2) ->
      let (e0, args) = strip_app_exp e in
      (match ExpW.exp_to_term e0 with
       | Constant cid when is_fw cid.descr && args <> [] ->
         (* record the FULL application's type once; skip the spine *)
         acc.th_sites <- (Typed_ast.exp_to_typ e, exp_to_locn e) :: acc.th_sites;
         List.iter go args
       | _ -> go e1; go e2)
    | Constant cid ->
      if is_fw cid.descr then
        (* bare / point-free reference: the demand is the (instantiated)
           codomain, reached through Tfn by typ_inhabited_bounds *)
        acc.th_sites <- (Typed_ast.exp_to_typ e, exp_to_locn e) :: acc.th_sites
      else
        acc.th_refs <- (cid.descr, cid.instantiation, exp_to_locn e) :: acc.th_refs
    | Lit l ->
      (match l.term with
       | L_undefined _ -> acc.th_sites <- (l.typ, exp_to_locn e) :: acc.th_sites
       | _ -> ())
    | Var _ | Nvar_e _ | Backend _ -> ()
    | Fun (_, _, _, e1) -> go e1
    | Function (_, pes, _) -> sl_iter (fun (_, _, e1, _) -> go e1) pes
    | Infix (e1, e2, e3) -> go e1; go e2; go e3
    | Record (_, fes, _) -> sl_iter (fun (_, _, e1, _) -> go e1) fes
    | Recup (_, e1, _, fes, _) -> go e1; sl_iter (fun (_, _, e2, _) -> go e2) fes
    | Field (e1, _, _) -> go e1
    | Vector (_, es, _) -> sl_iter go es
    | VectorSub (e1, _, _, _, _, _) -> go e1
    | VectorAcc (e1, _, _, _) -> go e1
    | Case (_, _, e1, _, pes, _) -> go e1; sl_iter (fun (_, _, e2, _) -> go e2) pes
    | Typed (_, e1, _, _, _) -> go e1
    | Let (_, lb, _, e1) ->
      (match lb with
       | (Let_val (_, _, _, e2), _) -> go e2
       | (Let_fun (_, _, _, _, e2), _) -> go e2);
      go e1
    | Tup (_, es, _) -> sl_iter go es
    | List (_, es, _) -> sl_iter go es
    | Paren (_, e1, _) -> go e1
    | Begin (_, e1, _) -> go e1
    | If (_, e1, _, e2, _, e3) -> go e1; go e2; go e3
    | Set (_, es, _) -> sl_iter go es
    | Setcomp (_, e1, _, e2, _, _) -> go e1; go e2
    | Comp_binding (_, _, e1, _, _, qbs, _, e2, _) ->
      go e1; List.iter go_qb qbs; go e2
    | Quant (_, qbs, _, e1) -> List.iter go_qb qbs; go e1
    | Do (_, _, dls, _, e1, _, _) ->
      List.iter (fun (Do_line (_, _, e2, _)) -> go e2) dls; go e1
  and go_qb = function
    | Qb_var _ -> ()
    | Qb_restr (_, _, _, _, e1, _) -> go e1
  in go e

(* One threading unit: the crefs a val_def group defines plus its scan.
   Fun_def clauses are grouped per constant (so and-chained siblings do
   not inherit each other's demands); a Let_def's bound names share the
   single body. *)
type thread_unit = {
  tu_crefs : Types.const_descr_ref list;
  tu_scan : thread_scan;
  tu_loc : Ast.l;
}

let lean_thread_cd_name (cd : const_descr) : string =
  Name.to_string (Path.get_name cd.const_binding)

(* The demand a scan makes RIGHT NOW: static failure-site demands plus,
   for every reference to an already-threaded def, the bounds of the
   instantiation types at the threaded positions. Errors are fail-closed
   generation-time failures naming the object and the escape hatches. *)
let lean_thread_demand env (where_ : string) (sc : thread_scan) : string list =
  let d = env.t_env in
  let union a b = a @ List.filter (fun x -> not (List.mem x a)) b in
  let dem = ref [] in
  List.iter (fun (t, l) ->
      match typ_inhabited_bounds d t with
      | Some names -> dem := union !dem names
      | None ->
        raise (Reporting_basic.err_general true l (Printf.sprintf
          "Lean backend: failure site (failwith/undefined default) in %s at type '%s' whose Inhabited instance cannot be derived; escape hatches: 'declare {lean} skip_instances' on the type plus a hand-written Lean instance, or a hand-written Lean target_rep"
          where_ (lean_typ_to_string t))))
    sc.th_sites;
  List.iter (fun (cref, inst, l) ->
      match lean_thread_lookup cref with
      | None -> ()
      | Some (poss, _) ->
        let callee = lean_thread_cd_name (c_env_lookup Ast.Unknown env.c_env cref) in
        List.iter (fun p ->
            match List.nth_opt inst p with
            | None -> ()
            | Some ti ->
              (match typ_inhabited_bounds d ti with
               | Some names -> dem := union !dem names
               | None ->
                 raise (Reporting_basic.err_general true l (Printf.sprintf
                   "Lean backend: call of '%s' (which carries an [Inhabited] binder) in %s at instantiation '%s' whose Inhabited instance cannot be derived; escape hatches: 'declare {lean} skip_instances' on the type plus a hand-written Lean instance, or a hand-written Lean target_rep"
                   callee where_ (lean_typ_to_string ti)))))
          poss)
    sc.th_refs;
  !dem

(* Clause grouping, SHARED between the failwith-thread pre-pass and the
   Fun_def emission path (and any future pre-pass that walks def
   groups — the supply pre-pass will be its third consumer): group a
   Fun_def's clauses by their defined constant (cref), preserving
   first-appearance order. Lem allows interleaved clauses of a rec-and
   block; Lean's equation compiler requires all clauses of one function
   in sequence. Keyed by cref, never by name string — two traversals
   grouping under different keys are a drift trap. *)
let lean_group_funcls (funcls : funcl_aux list)
    : (const_descr_ref * funcl_aux list) list =
  let order = ref [] in
  let tbl = Hashtbl.create 8 in
  List.iter (fun (((_, c, _, _, _, _) as fcl) : funcl_aux) ->
      (if not (Hashtbl.mem tbl c) then order := c :: !order);
      let existing = match Hashtbl.find_opt tbl c with Some v -> v | None -> [] in
      Hashtbl.replace tbl c (existing @ [fcl]))
    funcls;
  List.map (fun c -> (c, Hashtbl.find tbl c)) (List.rev !order)

(* Top-level definition names: a multi-name destructuring let
   (`let (a, b) = e`) is emitted as a synthesized `lemLetRhs_<names>`
   definition plus one projection per name, so a user definition with that
   prefix would collide with it. Refused at generation time, naming the
   definition (the reserved-name table above). *)
let lean_check_reserved_def_name l n =
  if lean_starts_with lean_reserved_let_rhs_prefix n then
    raise (Reporting_basic.err_general true l
      (Printf.sprintf "Lean backend: definition name '%s' uses the reserved '%s' prefix (synthesized destructuring-let RHS definitions; the reserved-name contract) — rename it" n lean_reserved_let_rhs_prefix))

(* Supply pre-pass: grow St.supply_lifted to a fixpoint over this
   module's Val_defs (the lean_reader_prepass pattern: Val_def
   granularity, nested modules recursed, instances skipped fail-closed
   at emission, set persists across modules in dependency order), and
   record each liftable def's THREADING ARITY (clause parameter count —
   the position of the result pair; consumed by the exact-application
   guard at threaded call sites). Two deliberate differences from the
   reader pre-pass:
   - reader_seed defs ARE liftable: a seed def may draw (its supply
     binder is independent of its reader-seed first argument);
   - defs carrying a Lean target_rep are EXCLUDED from lifting: their
     bodies render as block comments (dead text) and their call sites
     emit the hand-written rep, which cannot take a supply — threading
     their callers would inject state into a representation that
     ignores it. Their (dead) bodies render un-threaded inside the
     comment. *)
let lean_supply_prepass env (ds : def list) =
  if lean_supply_get_params env <> [] then begin
    let target = Target.Target_no_ident Target.Target_lean in
    let has_lean_rep cref =
      let cd = c_env_lookup Ast.Unknown env.c_env cref in
      Target.Targetmap.apply_target cd.target_rep target <> None in
    let rec def_infos acc (((d_aux, _), _, _) as d : def) =
      match d_aux with
      | Instance _ -> acc
      | Module (_, _, _, _, _, inner_ds, _) -> List.fold_left def_infos acc inner_ds
      | Val_def vd ->
        let defined = (add_def_entities target true empty_used_entities d).used_consts_set in
        if Types.Cdset.exists has_lean_rep defined then acc
        else begin
          (* A supply constant DEFINED by a live lem
             definition (no Lean target_rep, so the def would emit as
             an ordinary referenceable def) while its draw sites
             rewrite to LemLib.supplySplit is one constant with two
             semantics — fail closed. With a Lean rep the body renders
             as a block comment (dead text) and is excluded above. *)
          (match Types.Cdset.choose_opt
                   (Types.Cdset.filter (lean_supply_is_supply env) defined) with
           | Some c ->
             let cd = c_env_lookup Ast.Unknown env.c_env c in
             raise (Reporting_basic.err_general true cd.spec_l
               (Printf.sprintf
                 "Lean backend: supply val %s has a live lem definition and no Lean target_rep (the definition would emit as an ordinary def while draw sites rewrite to LemLib.supplySplit — one constant, two semantics; give it a Lean target_rep or keep it spec-only)"
                 (Name.to_string (Path.get_name cd.const_binding))))
           | None -> ());
          let used = (add_def_entities target false empty_used_entities d).used_consts_set in
          let arities = (match vd with
            | Fun_def (_, _, _, funcls) ->
              List.map (fun (c, fcls) ->
                  (c, match fcls with
                      | ((_, _, pats, _, _, _) : funcl_aux) :: _ -> List.length pats
                      | [] -> 0))
                (lean_group_funcls (Seplist.to_list funcls))
            | Let_def (_, _, (_, name_map, _, _, _)) ->
              List.map (fun (_, c) -> (c, 0)) name_map
            | Let_inline _ -> []) in
          (defined, used, arities) :: acc
        end
      | _ -> acc in
    let infos = List.rev (List.fold_left def_infos [] ds) in
    let changed = ref true in
    while !changed do
      changed := false;
      List.iter (fun (defined, used, arities) ->
          if not (Types.Cdset.subset defined !St.supply_lifted) then begin
            let needs =
              Types.Cdset.exists (lean_supply_is_supply env) used
              || not (Types.Cdset.is_empty
                        (Types.Cdset.inter used !St.supply_lifted)) in
            if needs then begin
              (* The [USER 2026-09-03] zero-discrepancy ruling: a drawing
                 top-level VALUE binding
                 is evaluated ONCE at module initialisation by the OCaml
                 reference, while state-passing would re-run its draws at
                 every use — no faithful lifting exists, so it is refused
                 (a loud refusal is not a divergence; a per-use def was). *)
              List.iter (fun (c, a) ->
                  if a = 0 then begin
                    let cd = c_env_lookup Ast.Unknown env.c_env c in
                    raise (Reporting_basic.err_general true cd.spec_l
                      (Printf.sprintf
                        "Lean backend: supply draw in the top-level VALUE binding '%s' (a definition without parameters) is unsupported: the OCaml reference evaluates a value binding once at module initialisation, whereas supply threading would draw afresh at every use — make it a function (e.g. of unit) so each call site draws explicitly"
                        (Name.to_string (Path.get_name cd.const_binding))))
                  end) arities;
              St.supply_lifted := Types.Cdset.union defined !St.supply_lifted;
              List.iter (fun (c, a) ->
                  St.supply_arity := Types.Cdmap.insert !St.supply_arity (c, a))
                arities;
              changed := true
            end
          end) infos
    done
  end

(* Pre-pass (runs after lean_inhabited_prepass, which populates the
   instance census this analysis reads): compute the threaded-def map to
   a fixpoint over this module's Val_defs, then guard-sweep Instance
   methods (rule 3). *)
let lean_failwith_thread_prepass env (ds : def list) =
  let target = Target.Target_no_ident Target.Target_lean in
  let in_lean targets = Typed_ast.in_targets_opt target targets in
  (* -- unit collection -- *)
  let scan_of_exps es =
    let sc = { th_sites = []; th_refs = [] } in
    List.iter (lean_thread_scan_exp env sc) es; sc in
  let units_of_val_def l (vd : val_def) : thread_unit list =
    match vd with
    | Let_def (_, targets, (_, name_map, _, _, e)) ->
      if in_lean targets then
        [{ tu_crefs = List.map snd name_map; tu_scan = scan_of_exps [e]; tu_loc = l }]
      else []
    | Fun_def (_, _, targets, funcls) ->
      if in_lean targets then begin
        (* shared cref-keyed clause grouping (the emission's rule) *)
        List.map (fun (c, fcls) ->
            let es = List.map (fun ((_, _, _, _, _, e) : funcl_aux) -> e) fcls in
            { tu_crefs = [c]; tu_scan = scan_of_exps es; tu_loc = l })
          (lean_group_funcls (Seplist.to_list funcls))
      end else []
    | Let_inline _ -> []  (* expanded at call sites by the inline macro *)
  in
  let rec collect acc (((d_aux, _), l, _) : def) =
    match d_aux with
    | Module (_, _, _, _, _, inner_ds, _) -> List.fold_left collect acc inner_ds
    | Val_def vd -> acc @ units_of_val_def l vd
    | _ -> acc
  in
  let units = List.fold_left collect [] ds in
  (* -- fixpoint -- *)
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun u ->
        let where_ =
          match u.tu_crefs with
          | c :: _ -> Printf.sprintf "'%s'" (lean_thread_cd_name (c_env_lookup Ast.Unknown env.c_env c))
          | [] -> "a definition" in
        let dem = lean_thread_demand env where_ u.tu_scan in
        if dem <> [] then
          List.iter (fun c ->
              let cd = c_env_lookup Ast.Unknown env.c_env c in
              let name = lean_thread_cd_name cd in
              (* phantom guard (rule 4): every demanded tyvar must occur
                 in the def's TYPE, or the binder would be unbound *)
              let sig_names =
                List.map (fun tv -> Name.to_string (Types.tnvar_to_name tv))
                  (Types.TNset.elements (Types.free_vars cd.const_type)) in
              List.iter (fun n ->
                  if not (List.mem n sig_names) then
                    raise (Reporting_basic.err_general true u.tu_loc (Printf.sprintf
                      "Lean backend: failure at type variable '%s' which does not occur in the signature of '%s' — cannot thread an [Inhabited %s] binder; determine the type variable at the failure site or give '%s' a hand-written Lean target_rep"
                      n name n name)))
                dem;
              let tp_names = List.map (fun tv -> Name.to_string (Types.tnvar_to_name tv)) cd.const_tparams in
              let poss = List.concat (List.mapi (fun i n -> if List.mem n dem then [i] else []) tp_names) in
              let names_in_order = List.filter (fun n -> List.mem n dem) tp_names in
              (match lean_thread_lookup c with
               | Some (old_poss, _) when old_poss = poss -> ()
               | _ ->
                 St.failwith_threaded := Types.Cdmap.insert !St.failwith_threaded (c, (poss, names_in_order));
                 if lean_thread_debug then
                   Printf.eprintf "THREAD %s [%s]\n%!" (Path.to_string cd.const_binding)
                     (String.concat "," names_in_order);
                 changed := true))
            u.tu_crefs)
      units
  done;
  (* -- instance guard sweep (rule 3): binders cannot be added to
        instance methods, so ANY non-empty demand inside one is a
        generation-time error naming the instance -- *)
  let rec guard (((d_aux, _), l, _) : def) =
    match d_aux with
    | Module (_, _, _, _, _, inner_ds, _) -> List.iter guard inner_ds
    | Instance (_, _, (_, _, _, class_path, _, _), vals, _) ->
      let inst_name = Path.to_string class_path in
      List.iter (fun vd ->
          let vd_units = units_of_val_def l vd in
          List.iter (fun u ->
              let where_ = Printf.sprintf "an instance of class '%s'" inst_name in
              let dem = lean_thread_demand env where_ u.tu_scan in
              if dem <> [] then
                raise (Reporting_basic.err_general true u.tu_loc (Printf.sprintf
                  "Lean backend: type-variable failure site (failwith/undefined default, or a call needing [Inhabited '%s']) inside a generated method of instance of class '%s' — instance methods cannot carry [Inhabited] binders; escape hatches: give the method a Lean target_rep ('declare lean target_rep function ...') or restructure so the failure is at a concrete type"
                  (String.concat "', '" dem) inst_name)))
            vd_units)
        vals
    | _ -> ()
  in List.iter guard ds

(* Run the analysis pre-passes over EVERY typechecked module
   of the invocation — including the non-output LIBRARY modules — in
   dependency order, BEFORE any emission (called from
   process_file.output). Rationale: analysis knowledge must span
   invocation boundaries. `make lean-libs` regenerates the library with
   [Inhabited] binders threaded onto its failure-carrying defs
   (fromJust, head, fail, find0, ...); a later cerberus/test invocation
   only EMITS its own modules, but its defs CALL those library defs —
   so caller-side demand computation must see the library's instance
   census and threading map. This pass recomputes that knowledge from
   the very library sources the invocation already typechecked and
   transformed: the same analysis that emitted the library, never a
   hardcoded list. The per-module pre-passes in lean_defs then re-run
   over each output module; all the passes are monotone (their
   sets/maps only grow, and re-insertions are equal), so the re-run is
   harmless. *)
let lean_analysis_prepass_all env (mods : checked_module list) =
  let saved = !St.current_module_name in
  List.iter (fun m ->
      let (mod_path, mod_name) = Path.to_name_list m.module_path in
      let module_name = Name.to_string
          (Backend_common.get_module_name env (Target.Target_no_ident Target.Target_lean) mod_path mod_name) in
      St.current_module_name := module_name;
      let (ds, _) = m.typed_ast in
      (* the same passes as lean_defs runs per output module, in its order *)
      lean_reader_prepass env ds;
      lean_ireader_prepass env ds;
      lean_cmp_prepass env ds;
      lean_fuel_prepass env ds;
      lean_supply_prepass env ds;
      lean_inhabited_prepass env ds;
      lean_failwith_thread_prepass env ds;
      lean_size_prepass env ds)
    mods;
  St.current_module_name := saved

(* A Lem comment `(* x *)` becomes `/- x -/`, keeping the source text,
   including its own spacing. The text is escaped so it cannot end the
   Lean comment early (`-/`) or open a nested one that never closes (`/-`),
   and padded so it cannot form `/--` (doc comment) or `/-!` (module doc). *)
(* Lem's lexer reads comment text as Latin-1 (lexer.mll, `Ulib.Text.of_latin1`;
   upstream report doc/upstream-tray draft 02), so each byte of a UTF-8
   character becomes a character of its own, and printing encodes each again:
   `§` (C2 A7) comes out as `Â§` (C3 82 C2 A7). Undo that for the Lean output,
   on each text fragment of a comment (a nested comment is its own fragment):
   decode the UTF-8, and if every character is below 256 and those bytes form
   valid UTF-8, they are the source text. Otherwise the text is kept as it is. *)
let undo_latin1_reading (s : string) : string =
  let n = String.length s in
  let out = Buffer.create n in
  let rec decode i =
    if i >= n then true
    else
      let c = Char.code s.[i] in
      if c < 0x80 then (Buffer.add_char out s.[i]; decode (i + 1))
      else if c land 0xE0 = 0xC0 && i + 1 < n && Char.code s.[i + 1] land 0xC0 = 0x80 then begin
        let cp = ((c land 0x1F) lsl 6) lor (Char.code s.[i + 1] land 0x3F) in
        if cp < 0x100 then (Buffer.add_char out (Char.chr cp); decode (i + 2)) else false
      end else false
  in
  let valid_utf8 t =
    let m = String.length t in
    let rec ok i =
      if i >= m then true
      else
        let c = Char.code t.[i] in
        let cont k = i + k < m && (let rec all j = j > k || (Char.code t.[i + j] land 0xC0 = 0x80 && all (j + 1)) in all 1) in
        if c < 0x80 then ok (i + 1)
        else if c land 0xE0 = 0xC0 && c >= 0xC2 then cont 1 && ok (i + 2)
        else if c land 0xF0 = 0xE0 then cont 2 && ok (i + 3)
        else if c land 0xF8 = 0xF0 && c <= 0xF4 then cont 3 && ok (i + 4)
        else false
    in
    ok 0
  in
  if not (String.exists (fun ch -> Char.code ch >= 0x80) s) then s
  else if decode 0 && valid_utf8 (Buffer.contents out) then Buffer.contents out
  else s

(* The text of a comment: a `/-` or `-/` written in it would open or close
   a Lean comment at the wrong depth, so a space is put between the two
   characters. Only the author's text is escaped; a comment nested in a
   comment is emitted with real delimiters (Lean's comments nest). *)
let escape_lean_comment_text (s : string) : string =
  let b = Buffer.create (String.length s + 8) in
  String.iteri (fun i c ->
      Buffer.add_char b c;
      let next = if i + 1 < String.length s then s.[i + 1] else ' ' in
      if (c = '/' && next = '-') || (c = '-' && next = '/') then Buffer.add_char b ' ')
    s;
  Buffer.contents b

(* `/- body -/`, padded so that the result is neither a docstring (`/--`)
   nor a module doc (`/-!`), and so that a body starting or ending with `-`
   cannot pair with a delimiter. *)
let wrap_lean_comment x =
  let body = Ulib.Text.to_string x in
  let is_space c = c = ' ' || c = '\n' || c = '\r' in
  let pre = if body <> "" && is_space body.[0] then "/-" else "/- " in
  let post = if body <> "" && is_space body.[String.length body - 1] then "-/" else " -/" in
  Ulib.Text.of_string (String.concat "" [pre; body; post])

(* Comments the backend writes itself start with `lem: ` (`/- lem: … -/`),
   so a reader can tell them from the author's comments. *)

(* In a binder list built by the backend (no comments or strings inside),
   adjacent implicit binders of one kind share a binder: `{a : Type} {b : Type}`
   becomes `{a b : Type}`. Only adjacent ones: the order of the arguments,
   and so the declaration's type, is unchanged. *)
let merge_implicit_binders (s : string) : string =
  let re = Str.regexp "{\\([^{}:]+\\) : \\(Type\\|Nat\\)} {\\([^{}:]+\\) : \\2}" in
  let rec fix s =
    let s' = Str.global_replace re "{\\1 \\3 : \\2}" s in
    if s' = s then s else fix s'
  in
  fix s

(* One `open` for a list of namespaces, wrapped at about 80 columns with an
   indented continuation: `open A B C` opens what `open A`, `open B`,
   `open C` do. *)
let open_line (nss : string list) : string =
  match nss with
  | [] -> ""
  | _ ->
    let b = Buffer.create 256 in
    Buffer.add_string b "open";
    let col = ref 4 in
    List.iter (fun ns ->
        if !col + 1 + String.length ns > 80 && !col > 4 then begin
          Buffer.add_string b "\n ";
          col := 1
        end;
        Buffer.add_char b ' '; Buffer.add_string b ns;
        col := !col + 1 + String.length ns)
      nss;
    Buffer.add_char b '\n';
    Buffer.contents b

(* Normalise the layout of a generated Lean file. Outside string literals,
   character literals and comments:
   - trailing spaces are removed, and runs of blank lines become one blank
     line;
   - inside a line, a run of spaces becomes one space; there is none after
     `(`/`[` or before `)`/`]`/`,`; `×` has one space on each side.
   The indentation at the start of a line is kept as it is. No token is
   added, removed or joined, so this changes no declaration; tokens move
   only along their own line (the declaration census checks the result).
   normalize_layout, below, runs this and then the layout pass
   (Lean_layout.reflow), which breaks long declarations over lines. *)
let normalize_spacing (s : string) : string =
  let n = String.length s in
  let b = Buffer.create n in
  let pending_spaces = Buffer.create 16 in
  let newlines = ref 0 in
  let last_char () = if Buffer.length b = 0 then '\n' else Buffer.nth b (Buffer.length b - 1) in
  (* [next] is the character about to be emitted *)
  let flush_ws next =
    if !newlines > 0 then begin
      Buffer.add_string b (if !newlines >= 2 then "\n\n" else "\n");
      newlines := 0;
      Buffer.add_buffer b pending_spaces
    end else if Buffer.length pending_spaces > 0 then begin
      let prev = last_char () in
      if prev = '(' || prev = '[' || prev = '\n' || next = ')' || next = ']' || next = ',' then ()
      else Buffer.add_char b ' '
    end;
    Buffer.clear pending_spaces
  in
  let is_ident_char c =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
    || c = '_' || c = '\'' || c = '.' || Char.code c >= 128
  in
  (* s.[i] = '(': if spaces, an atom and spaces then ')' follow, the atom and
     the index after ')'. An atom is [A-Za-z0-9_.'] with a letter, digit or
     `_` first; a numeral followed by `.` is not taken (`(1).f` vs `1.f`). *)
  let atom_in_parens i =
    let rec skip k = if k < n && s.[k] = ' ' then skip (k + 1) else k in
    let a0 = skip (i + 1) in
    let rec scan k =
      if k < n && (let c = s.[k] in (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
                                    || (c >= '0' && c <= '9') || c = '_' || c = '.' || c = '\'')
      then scan (k + 1) else k in
    let a1 = scan a0 in
    if a1 = a0 then None
    else
      let first = s.[a0] in
      if not ((first >= 'a' && first <= 'z') || (first >= 'A' && first <= 'Z')
              || (first >= '0' && first <= '9') || first = '_') then None
      else if s.[a1 - 1] = '.' then None
      else
        let close = skip a1 in
        if close < n && s.[close] = ')' then begin
          let a = String.sub s a0 (a1 - a0) in
          let numeral = first >= '0' && first <= '9' in
          if numeral && close + 1 < n && s.[close + 1] = '.' then None
          else Some (a, close + 1)
        end else None
  in
  (* `export T (C)` and `open N (x)` need their parentheses: is position i
     on a line whose first word is one of those commands? *)
  let in_export_or_open i =
    let ls = try String.rindex_from s i '\n' + 1 with Not_found -> 0 in
    let rec skip k = if k < n && s.[k] = ' ' then skip (k + 1) else k in
    let ls = skip ls in
    let starts p = let m = String.length p in ls + m <= n && String.sub s ls m = p in
    starts "export " || starts "open "
  in
  (* s.[i] = '\'': the index of the closing quote if a character literal
     starts here — an escape (`'\n'`, `'\''`, `'\x41'`) or one UTF-8
     character of one to four bytes (`'a'`, `'×'`) — else None. *)
  let char_literal_end i =
    if i + 1 >= n then None
    else if s.[i + 1] = '\\' then
      (try Some (String.index_from s (i + 3) '\'') with Not_found | Invalid_argument _ -> None)
    else begin
      let c = Char.code s.[i + 1] in
      let len = if c < 0x80 then 1 else if c land 0xE0 = 0xC0 then 2
        else if c land 0xF0 = 0xE0 then 3 else if c land 0xF8 = 0xF0 then 4 else 1 in
      if i + 1 + len < n && s.[i + 1 + len] = '\'' then Some (i + 1 + len) else None
    end
  in
  let rec copy_until_string_end i =
    (* s.[i-1] was the opening quote *)
    if i >= n then i
    else begin
      Buffer.add_char b s.[i];
      if s.[i] = '\\' && i + 1 < n then (Buffer.add_char b s.[i + 1]; copy_until_string_end (i + 2))
      else if s.[i] = '"' then i + 1
      else copy_until_string_end (i + 1)
    end
  in
  let rec copy_comment i depth =
    if i >= n then i
    else if depth = 0 then i
    else if i + 1 < n && s.[i] = '/' && s.[i + 1] = '-' then
      (Buffer.add_string b "/-"; copy_comment (i + 2) (depth + 1))
    else if i + 1 < n && s.[i] = '-' && s.[i + 1] = '/' then
      (Buffer.add_string b "-/"; copy_comment (i + 2) (depth - 1))
    else (Buffer.add_char b s.[i]; copy_comment (i + 1) depth)
  in
  let rec go i =
    if i >= n then ()
    else match s.[i] with
      | ' ' -> Buffer.add_char pending_spaces ' '; go (i + 1)
      | '\n' -> Buffer.clear pending_spaces; incr newlines; go (i + 1)
      | '"' -> flush_ws '"'; Buffer.add_char b '"'; go (copy_until_string_end (i + 1))
      | '/' when i + 1 < n && s.[i + 1] = '-' ->
          flush_ws '/'; Buffer.add_string b "/-"; go (copy_comment (i + 2) 1)
      | '-' when i + 1 < n && s.[i + 1] = '-' ->
          flush_ws '-';
          let j = try String.index_from s i '\n' with Not_found -> n in
          let line = String.sub s i (j - i) in
          let k = ref (String.length line) in
          while !k > 0 && line.[!k - 1] = ' ' do decr k done;
          Buffer.add_string b (String.sub line 0 !k); go j
      | '\'' when (i = 0 || not (is_ident_char s.[i - 1])) && char_literal_end i <> None ->
          (* a character literal is copied as it is *)
          flush_ws '\'';
          let j = match char_literal_end i with Some j -> j | None -> assert false in
          Buffer.add_string b (String.sub s i (j - i + 1)); go (j + 1)
      | '\xC2' when i + 1 < n && s.[i + 1] = '\xAB' ->
          (* `«…»`, one identifier whatever it contains: copied as it is *)
          flush_ws '\xC2';
          let rec close k = if k + 1 >= n then n else if s.[k] = '\xC2' && s.[k + 1] = '\xBB' then k + 2 else close (k + 1) in
          let j = close (i + 2) in
          Buffer.add_string b (String.sub s i (j - i)); go j
      | '\xC3' when i + 1 < n && s.[i + 1] = '\x97' && not (i + 2 < n && s.[i + 2] = '\'') ->
          (* `×`: one space on each side (the one after is dropped before `)`);
             `×'` is another token and is left alone *)
          if Buffer.length pending_spaces = 0 && !newlines = 0 then Buffer.add_char pending_spaces ' ';
          flush_ws '\xC3'; Buffer.add_string b "\xC3\x97";
          Buffer.add_char pending_spaces ' '; go (i + 2)
      | ':' when not (i + 1 < n && (s.[i + 1] = ':' || s.[i + 1] = '=')) && not (i > 0 && s.[i - 1] = ':') ->
          (* a lone `:` (a binder's or an ascription's) has a space on each
             side: `(x :(Nat × Nat))` → `(x : (Nat × Nat))` *)
          let prev = last_char () in
          if Buffer.length pending_spaces = 0 && !newlines = 0 && prev <> ' ' && prev <> '(' && prev <> '[' && prev <> '{'
          then Buffer.add_char pending_spaces ' ';
          flush_ws ':'; Buffer.add_char b ':';
          if i + 1 < n && (is_ident_char s.[i + 1] || s.[i + 1] = '(' || s.[i + 1] = '[' || s.[i + 1] = '{')
          then Buffer.add_char pending_spaces ' ';
          go (i + 1)
      | '(' when not (in_export_or_open i)
                 && (match atom_in_parens i with Some _ -> true | None -> false) ->
          (* `( atom )` is the atom: a name (possibly qualified) or a numeral *)
          (match atom_in_parens i with
           | Some (a, j) ->
             let prev = if Buffer.length pending_spaces > 0 || !newlines > 0 then ' ' else last_char () in
             flush_ws a.[0];
             if is_ident_char prev then Buffer.add_char b ' ';
             Buffer.add_string b a;
             (* a following `.` stays attached: `(x).1` is `x.1` *)
             if j < n && is_ident_char s.[j] && s.[j] <> '.' then Buffer.add_char pending_spaces ' ';
             go j
           | None -> assert false)
      | c -> flush_ws c; Buffer.add_char b c; go (i + 1)
  in
  go 0;
  if !newlines > 0 then Buffer.add_char b '\n';
  Buffer.contents b

(* The layout of a generated Lean file: token spacing (normalize_spacing),
   then line breaking and indentation (Lean_layout.reflow; the width is the
   Lean community's 100 columns). Both are text-only: the declaration
   census of the consumers is unchanged by them. *)
let lean_layout_width = 100

let normalize_layout (s : string) : string =
  Lean_layout.reflow ~width:lean_layout_width (normalize_spacing s)

(* Split a skip list at its first line break (in source order). The comments before it trail
   the previous item (same line); the comments after it lead the next item
   (one per line). The source whitespace itself is dropped: the backend owns
   the layout, the author owns the comments. *)
let split_skip_comments (s : Ast.lex_skips) : Ast.ml_comment list * Ast.ml_comment list =
  match s with
  | None -> ([], [])
  | Some ts ->
    let has_nl = function
      | Ast.Nl -> true
      | Ast.Ws r -> String.contains (Ulib.Text.to_string r) '\n'
      | Ast.Com _ -> false
    in
    let rec walk seen_nl trail lead = function
      | [] -> (List.rev trail, List.rev lead)
      | Ast.Com c :: rest ->
        if seen_nl then walk seen_nl trail (c :: lead) rest
        else walk seen_nl (c :: trail) lead rest
      | t :: rest -> walk (seen_nl || has_nl t) trail lead rest
    in
    (* Lem stores skips last-first (Output.ws renders them reversed). *)
    walk false [] [] (List.rev ts)

let comment_out c =
  if List.memq c !St.emitted_comments then Output.emp
  else begin
    St.emitted_comments := c :: !St.emitted_comments;
    Output.ws (Some [Ast.Com c])
  end

(* ` /- c -/` for each trailing comment. *)
let fresh_comments cs = List.filter (fun c -> not (List.memq c !St.emitted_comments)) cs

let trailing_comments cs =
  Output.flat (List.map (fun c -> Output.(^) (meta_utf8 " ") (comment_out c)) (fresh_comments cs))

(* `indent/- c -/\n` for each leading comment. *)
let leading_comments ~indent cs =
  Output.flat (List.map (fun c ->
      Output.flat [meta_utf8 indent; comment_out c; meta_utf8 "\n"]) (fresh_comments cs))

(* For alter_init_lskips: split a skip list into (whitespace, comments). *)
let take_comments (s : Ast.lex_skips) : Ast.lex_skips * Ast.lex_skips =
  match s with
  | None -> (None, None)
  | Some ts ->
    let (cs, ws_) = List.partition (function Ast.Com _ -> true | _ -> false) ts in
    if cs = [] then (s, None) else (Some ws_, Some cs)

(* The comments of a skip list inside an expression: `/- c -/ ` for each
   (Lean accepts a comment between any two tokens). The comment text is kept
   as written, line breaks included: the layout pass (Lean_layout.reflow)
   puts a multi-line comment on lines of its own, so no token can end up at
   the comment's last column (Lean's layout is column-sensitive: a `|` at a
   low column ends the enclosing match). Where that pass leaves a
   declaration as it was, it folds such a comment's line breaks to spaces
   instead. *)
let inline_comments (s : Ast.lex_skips) =
  let (t, l) = split_skip_comments s in
  let one c =
    St.emitted_comments := c :: !St.emitted_comments;
    Output.flat [Output.ws (Some [Ast.Com c]); meta_utf8 " "]
  in
  (* The comments that followed a line break in the source are preceded by
     one here (an Nl skip, so flatten_newlines folds it inside a match
     alternative): the layout pass puts such a comment on a line of its
     own before the code it leads, and re-joins the line where it leaves a
     declaration as it was. *)
  Output.flat (List.map one (fresh_comments t)
               @ List.map (fun c -> Output.flat [Output.new_line; one c]) (fresh_comments l))

(* Every comment of a skip list, laid out as at a top-level position: the
   trailing ones on the current line, the leading ones on their own lines. *)
let skip_comments_toplevel (s : Ast.lex_skips) =
  let (t, l) = split_skip_comments s in
  Output.flat [trailing_comments t;
               (if l = [] then Output.emp else meta_utf8 "\n");
               leading_comments ~indent:"" l]

(* Every skip list inside a source type, in source order. *)
let rec src_t_skips (t : Types.src_t) : Ast.lex_skips list =
  let id_skips (id : _ Types.id) = match id.Types.id_path with
    | Types.Id_none sk -> sk
    | Types.Id_some i -> Ident.get_lskip i
  in
  match t.Types.term with
  | Types.Typ_wild sk | Types.Typ_var (sk, _) -> [sk]
  | Types.Typ_len _ -> []
  | Types.Typ_fn (a, sk, b) -> src_t_skips a @ [sk] @ src_t_skips b
  | Types.Typ_tup ts ->
    let (_, pairs) = Seplist.to_pair_list None ts in
    List.concat_map (fun (t1, sk) -> src_t_skips t1 @ [sk]) pairs
  | Types.Typ_app (id, ts) | Types.Typ_backend (id, ts) ->
    id_skips id :: List.concat_map src_t_skips ts
  | Types.Typ_paren (s1, t1, s2) -> [s1] @ src_t_skips t1 @ [s2]
  | Types.Typ_with_sort (t1, _) -> src_t_skips t1

let init_comments (d : Typed_ast.def_aux) =
  let (_, s) = Typed_ast.def_aux_alter_init_lskips (fun s -> (s, s)) d in
  skip_comments_toplevel s

let sanitize_tabs r =
  let s = Ulib.Text.to_string r in
  if String.contains s '\t' then
    Ulib.Text.of_string (String.map (fun c -> if c = '\t' then ' ' else c) s)
  else r

let rec lean_comment_to_rope =
  function
    | Ast.Chars r ->
      sanitize_tabs (Ulib.Text.of_string (escape_lean_comment_text (undo_latin1_reading (Ulib.Text.to_string r))))
    | Ast.Comment coms ->
      (* a nested comment keeps its nesting; a `-` right before its `/-`
         would read as `-/`, so a space separates them *)
      let body = List.fold_left (fun acc c ->
          let piece = lean_comment_to_rope c in
          let acc_s = Ulib.Text.to_string acc in
          let needs_space = (match c with Ast.Comment _ -> true | Ast.Chars _ -> false)
                            && acc_s <> "" && acc_s.[String.length acc_s - 1] = '-' in
          Ulib.Text.(^^^) (if needs_space then Ulib.Text.(^^^) acc (r" ") else acc) piece)
          (r"") coms in
      wrap_lean_comment body

let lex_skip =
  function
    | Ast.Com r -> lean_comment_to_rope r
    | Ast.Ws r -> sanitize_tabs r
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

let from_string x = meta_utf8 x

(* Lean 4 forbids tab characters. Replace tabs with spaces in whitespace and comment tokens. *)
let ws s =
  let sanitize_skip = function
    | Ast.Ws r -> Ast.Ws (sanitize_tabs r)
    | Ast.Com _ as c -> c  (* Comments sanitized in lean_comment_to_rope *)
    | skip -> skip
  in
  match s with
  | None -> Output.ws None
  | Some ts -> Output.ws (Some (List.map sanitize_skip ts))

let sep x s = ws s ^ x
let path_sep = r"."

(* Source line breaks inside an expression become spaces; the backend lays
   the text out itself (normalize_layout, then Lean_layout.reflow). The
   line breaks inside comments are kept: the layout pass puts a multi-line
   comment on lines of its own. *)
let flatten_newlines = Output.flatten_newlines_keep_comments

let tyvar (_, tv, _) = id Type_var (Ulib.Text.(^^^) (r"") tv)
let concat_str s = concat (from_string s)

(* Escape a string if it's a Lean syntax keyword, using «» guillemets *)
let lean_escape_keyword s =
  if List.mem s lean_syntax_keywords then
    String.concat "" ["\xC2\xAB"; s; "\xC2\xBB"]  (* «name» *)
  else s

(* Record field names. A field is
   emitted in six places — the structure or single-constructor-inductive
   declaration, the projection, the literal, the update, the mutual-record
   accessor and the positional update of a mutual record — and every one
   goes through lean_escape_keyword, so a field named like a Lean keyword
   («at», «from», «by», «show», …) is spelled the same way everywhere (the
   declaration used to be emitted bare, a Lean parse error).

   Names that Lean itself declares in every structure's or inductive's
   namespace cannot be fields at all: `mk` is "the name of the structure
   constructor", the others make the kernel report "constant has already
   been declared" (`below`/`brecOn` for recursive records; measured on Lean
   4.32.2 for a structure, a recursive structure and the single-constructor
   inductive with accessors, in the three shapes the backend emits).
   Escaping cannot help («rec» is rec), the reserved-name pass does not
   rename fields (DESIGN, "Reserved-name avoidance"), so such a field is
   refused at generation, naming the field and the Lean declaration. *)
let lean_structure_generated_names =
  ["mk"; "rec"; "recOn"; "casesOn"; "noConfusion"; "noConfusionType"; "below"; "brecOn"]

(* Lean 4.32.2 runtime limit: a binary built from a structure or
   constructor with 128 or more
   fields segfaults when it allocates such an object at run time — the
   object header plus 128 pointer-sized fields is 1032 bytes, past the
   runtime allocator's 1024-byte small-object limit, and the allocation
   path does not check it. Reproduced in plain Lean (no LemLib): a
   128-field structure of Nat and a 128-argument constructor crash; 127
   Nat fields work; 127 Nat fields plus one Bool (1025 bytes) crash; 128
   or 200 Bool fields (one byte each) work. The refusal counts every field
   at the pointer size, the upper bound of what a field can occupy, so it
   admits exactly the widths that cannot reach the limit (over-refusing a
   wide record of one-byte fields, loudly). Not a magic value in DESIGN's
   sense: it mirrors a limit of the Lean runtime, not a choice about the
   semantics. *)
let lean_max_constructor_fields = 127

let lean_check_constructor_width l (kind : string) (type_name : string) (ctor : string option) (n : int) =
  if n > lean_max_constructor_fields then
    raise (Reporting_basic.err_general true l
      (Printf.sprintf
        "Lean backend: %s `%s`%s has %d fields; a Lean 4.32.2 binary segfaults at run time when it allocates a constructor object of 128 or more fields (object header plus 128 pointer-sized fields = 1032 bytes exceeds the runtime allocator's 1024-byte small-object limit; reproduced in plain Lean), so the Lean target refuses more than %d — split the %s"
        kind type_name (match ctor with Some c -> Printf.sprintf " (constructor `%s`)" c | None -> "")
        n lean_max_constructor_fields kind))

let lskips_t_to_output name =
  let stripped = Name.strip_lskip name in
  let s = Ulib.Text.to_string (Name.to_rope stripped) in
  let escaped = lean_escape_keyword s in
  if escaped <> s then from_string escaped
  else Output.id Term_var (Name.to_rope stripped)
;;

(* Name output for variables with keyword escaping *)
let name_var_output v =
  let s = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip v)) in
  let escaped = lean_escape_keyword s in
  if escaped <> s then
    Output.flat [ws (Name.get_lskip v); from_string escaped]
  else
    Name.to_output Term_var v

(* A record in a mutual block is a Lean `structure`, unless the block's
   members have different numbers of type parameters. Such a block is
   emitted with the parameters as INDICES (type_def_indexed), and a Lean
   structure cannot have indices, so there the record is a single-constructor
   inductive (forced). St.mutual_records lists exactly those records. *)
let mutual_block_records_as_inductives (defs : (_ * Typed_ast.tnvar list * _ * _ * _) list) =
  match List.map (fun (_, tvs, _, _, _) -> List.length tvs) defs with
  | [] -> false
  | x :: xs -> not (List.for_all (fun y -> y = x) xs)

let lean_record_is_inductive path =
  List.exists (fun p -> Path.compare p path = 0) !St.mutual_records

(* If the type is a record rendered as a single-constructor inductive (see
   above), return its path. St.mutual_records accumulates across the files
   of one lem invocation. *)
let mutual_record_path typ : Path.t option =
  match typ.Types.t with
    | Types.Tapp (_, path) ->
        if List.exists (fun p -> Path.compare p path = 0) !St.mutual_records
        then Some path
        else None
    | _ -> None

let in_target targets = Typed_ast.in_targets_opt (Target.Target_no_ident Target.Target_lean) targets;;

let lean_infix_op a x =
  Output.flat [
    from_string "(fun x y => x "; id a x; from_string " y)"
  ]
;;

let lean_format_op use_infix a x =
  if use_infix then
    lean_infix_op a x
  else
    id a x


let generate_fresh_name () =
  let n = !St.fresh_name_counter in
  St.fresh_name_counter := n + 1;
  Stdlib.(^) "x" (string_of_int n)

type variable
  = Tyvar of Output.t
  | Nvar of Output.t

let tnvar_to_variable = function
  | Typed_ast.Tn_A _ as tv -> Tyvar (from_string (tnvar_to_string tv))
  | Typed_ast.Tn_N _ as nv -> Nvar (from_string (tnvar_to_string nv))
;;

module LeanBackendAux (A : sig val avoid : var_avoid_f option;; val env : env;; val dir : string;; val ascii_rep_set : Types.Cdset.t end) =
  struct

    module B = Backend_common.Make (
      struct
        let env = A.env
        let target = Target_no_ident Target_lean
        let id_format_args = (lean_format_op, path_sep)
        let dir = A.dir
      end);;

    module C = Exps_in_context (
      struct
        let env_opt = Some A.env
        let avoid = A.avoid
      end)
    ;;

(* Extract (class_name, type_var_name) pairs from @Class.method patterns
   in a TYR_subst RHS src_t. These patterns indicate that the type requires
   a typeclass instance parameter (e.g., @Size.size 'a _ means [Size 'a]). *)
let collect_class_constraints_from_src_t (st : Types.src_t) : (string * string) list =
  let rec collect (t : Types.src_t) = match t.term with
    | Types.Typ_backend (p, args) ->
      let path_str = Path.to_string p.descr in
      let at_constraints =
        if String.length path_str > 1 && path_str.[0] = '@' then
          match String.index_opt path_str '.' with
          | Some dot_pos ->
            let class_name = String.sub path_str 1 (dot_pos - 1) in
            List.filter_map (fun (arg : Types.src_t) ->
              match arg.term with
              | Types.Typ_var (_, v) ->
                Some (class_name, Ulib.Text.to_string (Types.tnvar_to_rope (Types.Ty v)))
              | _ -> None
            ) args
          | None -> []
        else []
      in
      at_constraints @ List.concat_map collect args
    | Types.Typ_app (_, args) -> List.concat_map collect args
    | Types.Typ_paren (_, t', _) -> collect t'
    | Types.Typ_fn (t1, _, t2) -> collect t1 @ collect t2
    | Types.Typ_tup sl -> List.concat_map collect (Seplist.to_list sl)
    | _ -> []
  in
  collect st
;;

(* Collect extra class constraints introduced by TYR_subst type target reps.
   When a type like mword has a TYR_subst mapping to BitVec (@Size.size 'a _),
   any function using mword 'a needs [Size 'a] but the Lem type doesn't
   carry this constraint. This function walks a Lem type and finds all such
   extra constraints by: (1) finding Tapp nodes whose type has a Lean TYR_subst,
   (2) extracting @Class.method patterns from the TYR_subst RHS via
   collect_class_constraints_from_src_t, (3) mapping TYR_subst type variables
   to actual type arguments. *)
let extra_constraints_for_tyr_subst (ty : Types.t) : (string * string) list =
  let constraints = ref [] in
  let rec walk (ty : Types.t) =
    match ty.t with
    | Types.Tapp (args, path) ->
      begin match Types.type_defs_lookup_tc A.env.t_env path with
      | Some (Types.Tc_type td) ->
        begin match Target.Targetmap.apply_target td.Types.type_target_rep
                (Target.Target_no_ident Target.Target_lean) with
        | Some (Types.TYR_subst (_, _, tvars, rhs_t)) ->
          let tvar_strs = List.map (fun tv ->
            Ulib.Text.to_string (Types.tnvar_to_rope tv)
          ) tvars in
          let var_map = List.combine tvar_strs args in
          let raw = collect_class_constraints_from_src_t rhs_t in
          List.iter (fun (cls, tv) ->
            match List.assoc_opt tv var_map with
            | Some actual_ty ->
              begin match actual_ty.t with
              | Types.Tvar v' ->
                let actual_tv = Ulib.Text.to_string (Tyvar.to_rope v') in
                if not (List.mem (cls, actual_tv) !constraints) then
                  constraints := (cls, actual_tv) :: !constraints
              | _ -> () (* Concrete type argument — no constraint needed *)
              end
            | None -> ()
          ) raw
        | _ -> ()
        end
      | Some (Types.Tc_class _) -> () (* Classes don't have TYR_subst *)
      | None -> ()
      end;
      List.iter walk args
    | Types.Tfn (t1, t2) -> walk t1; walk t2
    | Types.Ttup ts -> List.iter walk ts
    | Types.Tbackend (ts, _) -> List.iter walk ts
    | _ -> ()
  in
  walk ty;
  List.rev !constraints
;;

(* Filter out constraints that are already present in Lem's class_constraints. *)
let filter_new_tyr_constraints extras class_constraints =
  let existing = List.map (fun (path, tnvar) ->
    (Name.to_string (B.class_path_to_name path),
     Ulib.Text.to_string (Types.tnvar_to_rope tnvar))
  ) class_constraints in
  List.filter (fun c -> not (List.mem c existing)) extras
;;

(* Format extra TYR_subst constraints as Lean instance parameters: [Class tv] *)
let format_tyr_constraints extras =
  Output.flat (List.map (fun (cls, tv) ->
    Output.flat [from_string " ["; from_string cls; from_string " "; from_string tv; from_string "]"]
  ) extras)
;;

(* Lean-native constraints for default instances.
   Lem's default_instance declarations are unconstrained (forall 'a), but
   their method bodies reference Lean functions requiring typeclass instances:
   - Eq0 body uses == (BEq) and != (BEq)
   - SetType body uses defaultCompare (Ord)
   The other two defaults (OrdMaxMin, MapKeyType) already carry Lem-level
   constraints that provide what Lean needs.
   This extends the extra_constraints_for_tyr_subst pattern (above) to
   handle function target rep constraints in default instances. *)
let lean_default_instance_extra_constraints class_name =
  match class_name with
  | "Eq0" -> ["BEq"]
  | "SetType" -> ["Ord"]
  | _ -> []
;;

(* Symbolic constant names. Lean cannot define or
   reference a constant named `>>=`: `def >>= ...` is a parse error, and an
   infix `x >>= f` silently resolves to Lean's own `Bind` operator instead of
   the Lem constant. A SHOWN constant (no Lean target rep) whose Lean name is
   not a Lean identifier is therefore always rendered by its ASCII
   representation (`declare {lean} ascii_rep function (>>=) = `bind_name``),
   at its definition AND at every use (Lem's generic machinery applies ASCII
   names only at definition sites, the backend's `ascii_rep_set`, since the
   other targets accept symbolic names at uses). Without an ASCII rep the
   definition is refused at generation time: `lean_symbolic_def_check`. *)
(* A Lean 4 atomic identifier: a letter or `_` first, then letters, digits,
   `_`, `'`, `!`, `?` (Lean's `isIdFirst`/`isIdRest`); bytes >= 0x80 are
   accepted as parts of Unicode letters. Deliberately NOT Lem's
   `Util.is_simple_ident_string`, which rejects the `'` Lean allows. *)
let is_lean_ident_string (s : string) : bool =
  let first c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_' || Char.code c >= 0x80 in
  let rest c = first c || (c >= '0' && c <= '9') || c = '\'' || c = '!' || c = '?' in
  String.length s > 0 && first s.[0] &&
  (let ok = ref true in String.iteri (fun i c -> if i > 0 && not (rest c) then ok := false) s; !ok)
;;

let lean_symbolic_name (cd : const_descr_ref) : (string * bool) option =
  let c_descr = c_env_lookup Ast.Unknown A.env.c_env cd in
  let (is_shown, n, n_ascii_opt) =
    constant_descr_to_name (Target.Target_no_ident Target.Target_lean) c_descr in
  let s = Name.to_string n in
  if is_shown && not (is_lean_ident_string s) then Some (s, n_ascii_opt <> None)
  else None
;;

let use_ascii_rep_for_const (cd : const_descr_ref) : bool =
  Types.Cdset.mem cd A.ascii_rep_set ||
  (match lean_symbolic_name cd with Some (_, has_ascii) -> has_ascii | None -> false)
;;

let lean_symbolic_def_check (cd : const_descr_ref) : unit =
  match lean_symbolic_name cd with
  | Some (s, false) when not !St.rendering_comment ->
    let l = (c_env_lookup Ast.Unknown A.env.c_env cd).spec_l in
    raise (Reporting_basic.err_general true l
      (String.concat "" ["Lean backend: constant `"; s;
        "` has a symbolic name, which is not a Lean identifier (a definition `def "; s;
        "` does not parse, and an infix use would resolve to a Lean operator); give it an ASCII name with `declare {lean} ascii_rep function ("; s;
        ") = `name``"]))
  | _ -> ()
;;

let field_ident_to_output fd ascii_alternative =
  let ident = B.const_id_to_ident fd ascii_alternative in
  let name = Ident.get_name ident in
  let stripped = Name.strip_lskip name in
    from_string (lean_escape_keyword (Name.to_string stripped))
;;

(* The declaration-side spelling of a record field: the same escaping as
   the projection/literal/update side above (lean_structure_generated_names). *)
let field_decl_output n f_ref =
  from_string (lean_escape_keyword (Name.to_string (Name.strip_lskip (B.const_ref_to_name n false f_ref))))
;;

(* the Lean names a type constructor path can print as: its Lean name, and
   the components of its Lean target representation (an identifier, or the
   type constructors of a substituted type, one level) *)
let lean_type_path_names env ((p, backend) : Path.t * bool) : string list =
  let components i = let (ms, n) = Ident.to_name_list i in List.map Name.to_string (n :: ms) in
  if backend then (let (ms, n) = Path.to_name_list p in List.map Name.to_string (n :: ms))
  else
    let own = Name.to_string (Name.strip_lskip (B.type_path_to_name (Name.add_lskip (Path.get_name p)) p)) in
    let rep_of q =
      match Types.Pfmap.apply env.t_env q with
      | Some (Types.Tc_type td) ->
        Target.Targetmap.apply_target td.Types.type_target_rep (Target.Target_no_ident Target.Target_lean)
      | Some (Types.Tc_class _) | None -> None in
    own :: (match rep_of p with
      | Some (Types.TYR_simple (_, _, i)) -> components i
      | Some (Types.TYR_subst (_, _, _, st)) ->
        List.concat_map (fun (q, b) ->
            if b then (let (ms, n) = Path.to_name_list q in List.map Name.to_string (n :: ms))
            else
              Name.to_string (Name.strip_lskip (B.type_path_to_name (Name.add_lskip (Path.get_name q)) q))
              :: (match rep_of q with Some (Types.TYR_simple (_, _, i)) -> components i | _ -> []))
          (lean_src_t_type_paths st)
      | None -> [])

let lean_tyvar_renames_for env (tv_set : Types.TNset.t) (pats : pat list) (exps : exp list)
    : (string * string) list =
  let tyvars = List.filter_map (fun tv -> match tv with
      | Types.Ty _ -> Some (tnvar_name tv) | Types.Nv _ -> None) (Types.TNset.elements tv_set) in
  if tyvars = [] then [] else begin
    let names = ref [] in
    let add s = if not (List.mem s !names) then names := s :: !names in
    let add_typ ty = List.iter (fun pb -> List.iter add (lean_type_path_names env pb)) (lean_typ_type_paths ty) in
    List.iter (fun p -> List.iter add_typ (lean_types_of_pat p)) pats;
    List.iter (fun e ->
        List.iter add_typ (lean_types_of_exp e);
        List.iter (fun (c : const_descr_ref id) ->
            let cd = c_env_lookup Ast.Unknown env.c_env c.descr in
            let n0 = Name.add_lskip (Path.get_name cd.const_binding) in
            add (Name.to_string (Name.strip_lskip (B.const_ref_to_name n0 false c.descr))))
          (exp_constants e))
      exps;
    let colliding = List.filter (fun tv -> List.mem tv !names) tyvars in
    if colliding = [] then [] else begin
      let bound =
        List.concat_map exp_bound_names exps
        @ List.concat_map (fun p -> List.map Name.to_string (NameSet.elements (Typed_ast.pat_to_bound_names p))) pats in
      let chosen = ref [] in
      let taken n =
        List.mem n !names || List.mem n tyvars || List.mem n bound || List.mem n !chosen
        || lean_is_reserved_name n in
      List.map (fun tv ->
          let rec pick c = let c = Stdlib.(^) c "'" in if taken c then pick c else c in
          let c = pick tv in
          chosen := c :: !chosen; (tv, c))
        colliding
    end
  end

(* Lean 4's greedy parser extends match/if/let/fun rightward, consuming
   subsequent tokens. These forms must be parenthesized when nested inside:
   - function arguments: f (match ...) instead of f match ...
   - match arm bodies: | p => (match ...) to avoid consuming outer | arms
   - if conditions: if (match ...) then ... to avoid misparsing *)
(* If/else-if chains longer than this are split
   into blocks of [lean_if_chain_block] arms (see the If renderer). Lean's
   limit is ~128 levels; the margin covers chains nested in other terms. *)
(* Lem's `if` takes a `bool`. Emitted as Lean's
   `if c then ...`, it relied on the Bool->Prop coercion plus a Decidable
   instance search, both instance problems that Lean elaborates behind
   `wait_if_type_mvar%` and that can get STUCK depending on context
   (linksem link.lem: "Application type mismatch ... Bool ... expected
   Prop"; the coercion problem `CoeT Bool c Prop` mentions the condition
   term, which mentioned a let-variable whose value still had a postponed
   match). LemLib's `lem_if c then t else e` expands to
   `@ite _ (c = true) (instDecidableEqBool _ _) t e`: no instance search,
   the condition written once, and the SAME kernel term Lean elaborates for
   a Bool `if` (pinned in LemLibTest). Where conditions are rendered as
   Prop (indreln premises, St.prop_equality) the builtin `if` stays. *)
let lean_if_kw () = if !St.prop_equality then "if" else "lem_if"

let lean_if_chain_max = 96
let lean_if_chain_block = 64

let needs_parens term =
  match term with
    | Case _ | If _ | Let _ | Fun _ -> true
    | _ -> false

(* Pattern rendering has two modes:
   - FunParam: adds type annotations to variables and wildcards (needed with
     autoImplicit=false), resolves wildcard types, wraps cons/unit in parens
   - MatchArm: bare output for match arms and let bindings *)
type pat_style = FunParam | MatchArm

    (* --- Reader lifting helpers (declare {lean} reader val) ---
       thin wrappers over the top-level env-parameterized versions;
       the pre-pass lives at module-emission level (lean_reader_prepass). *)
    let is_reader_cref = lean_reader_is_reader A.env
    let is_seed_cref = lean_reader_is_seed A.env
    let is_consumer_cref = lean_reader_is_consumer A.env
    let reader_param_name = lean_reader_param_name A.env
    let get_reader_params () = lean_reader_get_params A.env

    (* A reader val has type unit -> T; the parameter carries T. *)
    let reader_value_typ cref =
      let cd = c_env_lookup Ast.Unknown A.env.c_env cref in
      match cd.const_type.Types.t with
      | Types.Tfn (_, cod) -> cod
      | _ -> cd.const_type

    (* Does this expression force reader lifting of its enclosing def:
       a direct reader use, or a call to an already-lifted def. *)
    let exp_needs_reader (e : exp) : bool =
      let ue = add_exp_entities empty_used_entities e in
      List.exists (fun cref ->
          is_reader_cref cref || is_consumer_cref cref
          || Types.Cdset.mem cref !St.reader_lifted)
        ue.used_consts

    (* reader_consumer scope guard (RC-rel and friends): a consumer call
       site needs reader VALUES to pass — available only inside a
       reader-lifted def (the binders) or a reader_seed def (the seed
       arguments). Everywhere else (indreln rules, lemmas/asserts,
       instance methods reach the instance error first) is a fail-closed
       generation-time error. Inert for block comments and vacuous when
       no reader is declared (nothing to inject). *)
    let reader_consumer_scope_check (l : Ast.l) : unit =
      if get_reader_params () <> []
         && not (!St.reader_binder || !St.reader_seed_param <> None
                 || !St.rendering_comment) then
        raise (Reporting_basic.err_general true l
          "Lean backend: reader_consumer call outside a reader-injection scope (unsupported: indreln rules, lemmas/asserts, and other non-lifted contexts have no reader value to pass — RC-rel/RC-scope)")

    (* Injection value name: the enclosing def's injected parameter, or —
       inside a reader_seed def — the seed parameter associated with THIS
       reader's binder (N-ary seeding: one seed per declared reader, keyed
       by the injected binder name). The association is total over
       get_reader_params () by construction (seed_info), so a miss inside
       a seed def is an internal invariant violation: fail closed, never
       fall back to the binder there (the binder does not exist in a
       non-lifted seed def). *)
    let reader_inject_name pname =
      match !St.reader_seed_param with
      | None -> pname
      | Some assoc ->
        (match List.assoc_opt pname assoc with
         | Some seed -> seed
         | None ->
           raise (Reporting_basic.err_general true Ast.Unknown
             (Printf.sprintf
               "Lean backend: internal error — reader binder '%s' has no seed inside a reader_seed def (the seed association is built over every declared reader; report this)"
               pname)))

    let reader_args_output () =
      Output.flat (List.map (fun (_, pname) ->
          Output.flat [from_string " "; from_string (reader_inject_name pname)])
        (get_reader_params ()))

    (* --- Fuel lifting helpers (declare {lean} fuel val / fuel_consumer
       val; the mechanism comment is at lean_fuel_is_fuelled). --- *)
    let is_fuel_consumer_cref = lean_fuel_is_consumer A.env
    (* declare {lean} fuel_measure val (mechanism comment at lean_fuel_measure_for) *)
    let fuel_measure_for = lean_fuel_measure_for A.env
    let is_ambient_fuelled_cref = lean_fuel_is_ambient A.env
    (* declare {lean} structural val (mechanism comment at lean_is_structural) *)
    let is_structural_cref = lean_is_structural A.env

    (* ===== Point-free `function` tails =====

       `let rec f acc = function | [] -> … | x :: xs -> f (acc + x) xs`
       recurses on a list that is the anonymous scrutinee of a trailing
       `function`, not a named parameter: after lem's pattern compilation
       the clause body is `fun x -> match x with …` (Patterns.remove_function,
       a fresh `x`), the head binds one parameter fewer than the type has
       arrows, and neither the structural-parameter analysis (which ranges
       over the head's parameters) nor a fuel measure (an expression over
       the parameters) can name the recursion argument. [USER 2026-09-04]
       "we don't change the lem structure for ocaml": the `.lem` is not
       eta-expanded — the LEAN EMISSION is. For a definition that carries
       `declare {lean} fuel_measure val` or `declare {lean} structural val`
       (nothing else changes: an ambient fuel'd or plain definition renders
       as before), the trailing binders are hoisted into the head:

         def f (acc : Nat) : List Nat → Nat := fun (x : List Nat) => match x with …
         def f (acc : Nat) (lemTail : List Nat) : Nat := match lemTail with …

       ONE fresh binder per `function` — its scrutinee — named `lemTail`
       (deterministic: the macro's `x`/`x1`/… depends on which names are
       free in the body, and a measure must be able to name the binder
       from the `.lem`: ``fuel_measure val f = `List.length lemTail + 1` ``);
       a user-written `fun y ->` under which the `function` sits is hoisted
       with the user's name (`let f acc = fun y -> function …` binds
       `acc`, `y`, `lemTail`). Hygiene, fail-closed: `lemTail` is refused if
       it is a parameter, a binder or a free variable anywhere in the
       clause body, or the lem name of a constant the body references; a
       user binder is refused if it would shadow a parameter or be captured
       by the destructuring pattern it is hoisted through. Hoisting is
       through a Paren and through the SINGLE-arm match that lem's pattern
       compiler emits for a destructuring parameter (`let rec f (a, b) =
       function …` ↦ `match p with | (a, b) => fun x => …`) — an
       irrefutable match on a parameter variable with a lambda body is
       extensionally the lambda over the match; nothing else is descended.
       The head's declared result type loses one arrow per hoisted binder
       (the annotation's own `Typ_fn` when it has one, else the
       typechecker's codomain). The fuel sentinel (`declare {lean} fuel
       val f = `payload` `) is written at the head's ORIGINAL codomain — a
       function — so the worker's exhaustion arm and the `_zero` lemma
       apply it to the hoisted binders (`((payload) lemTail)`, definitionally
       the same value). Refused (unsupported) on a supply-lifted
       definition: the supply prepass records the pre-hoist arity for the
       call-site threading. The OCaml (and every non-Lean) emitter never
       sees any of this. *)
    let lean_tail_binder = lean_reserved_tail_name
    let lean_hoist_tail_binders inside_instance (g : funcl_aux list) : funcl_aux list =
      match g with
      | [(nla, c, pats, typ_opt, sk, e)]
        when (not !St.rendering_comment) && not inside_instance
             && (fuel_measure_for c <> None || is_structural_cref c) ->
        let l = locn_of_clause_group g in
        let fname = Name.to_string (Name.strip_lskip nla.term) in
        let refuse msg =
          raise (Reporting_basic.err_general true l
            (Printf.sprintf "Lean backend: point-free `function` tail of %s: %s" fname msg)) in
        let nm x = Name.to_string (Name.strip_lskip x) in
        let pat_names p = List.map (fun a -> nm a.term) (Pattern_syntax.pat_vars_src p) in
        let param_var (p : pat) = match lean_strip_pat p with
          | P_var v | P_var_annot (v, _) -> Some (nm v)
          | _ -> None in
        let rec strip e = match C.exp_to_term e with
          | Paren (_, e', _) -> strip e'
          | _ -> e in
        let is_remove_function e = match Typed_ast.exp_to_locn e with
          | Ast.Trans (_, "remove_function", _) -> true
          | _ -> false in
        (* what the synthesized binder must not collide with *)
        let body_bound = exp_bound_names e in
        let body_free = Nfmap.fold (fun acc k _ -> Name.to_string k :: acc) [] (C.exp_to_free e) in
        let body_consts = List.map (fun cr ->
            Name.to_string (Path.get_name (c_env_lookup Ast.Unknown A.env.c_env cr).const_binding))
            (add_exp_entities empty_used_entities e).used_consts in
        let rec strip_typ_paren (t : src_t) = match t.term with
          | Typ_paren (_, t', _) -> strip_typ_paren t'
          | _ -> t in
        (* the result annotation after one more head binder *)
        let typ_after typ_opt (cod : Types.t) = match typ_opt with
          | None -> None
          | Some (s, t) ->
            (match (strip_typ_paren t).term with
             | Typ_fn (_, _, t2) -> Some (s, t2)
             | _ -> Some (s, C.t_to_src_t cod)) in
        let tail_name = Name.add_lskip (Name.from_string lean_tail_binder) in
        (* hoist : pats so far -> annotation -> clause body -> the pattern
           variables of every destructuring match hoisted through -> hoisted
           names so far -> (pats, annotation, residual body, hoisted) *)
        let rec hoist pats typ_opt e enclosing hoisted =
          let e' = strip e in
          match C.exp_to_term e' with
          | Fun (_, ps, _, body) when ps <> [] && List.for_all (fun p -> param_var p <> None) ps ->
            let ps, body =
              if not (is_remove_function e') then ps, body
              else begin
                (* the macro's shape is `fun x -> match x with …` with a
                   fresh x: rename the binder and the scrutinee to lemTail *)
                match ps, C.exp_to_term (strip body) with
                | [p], Case (b, cs1, scrut, cs2, arms, cs3) ->
                  (match param_var p, C.exp_to_term (strip scrut) with
                   | Some x, Var v when nm v = x ->
                     let clash where =
                       refuse (Printf.sprintf "the scrutinee binder `%s` synthesized for the eta-expansion (the measured or structural emission names the `function` argument so a measure or the structural analysis can see it) would %s — rename that variable" lean_tail_binder where) in
                     if List.exists (fun q -> param_var q = Some lean_tail_binder) pats
                        || List.mem lean_tail_binder hoisted then clash "shadow a parameter of the same name";
                     if List.mem lean_tail_binder enclosing then clash "be captured by a destructuring pattern of a parameter it sits under";
                     if List.mem lean_tail_binder body_bound then clash "collide with a binder of the same name in the body";
                     if List.mem lean_tail_binder body_free then clash "capture a free variable of the same name in the body";
                     if List.mem lean_tail_binder body_consts then clash "capture a constant of the same name referenced in the body";
                     (* what the body's constants RENDER as — a Lean
                        target_rep spelled `lemTail` *)
                     lean_reserved_capture_check A.env l fname e;
                     let p' = C.mk_pvar p.locn tail_name p.typ in
                     let scrut' = C.mk_var (Typed_ast.exp_to_locn scrut) tail_name p.typ in
                     let body' = C.mk_case b (Typed_ast.exp_to_locn body) cs1 scrut' cs2 arms cs3
                         (Some (Typed_ast.exp_to_typ body)) in
                     [p'], body'
                   | _ -> refuse "internal error — the compiled `function` is not `fun x -> match x with …`")
                | _ -> refuse "internal error — the compiled `function` binds more than one variable"
              end in
            let names = List.map (fun p -> match param_var p with Some v -> v | None -> "") ps in
            List.iter (fun v ->
                if List.exists (fun q -> param_var q = Some v) pats || List.mem v hoisted then
                  refuse (Printf.sprintf "hoisting the binder `%s` of the trailing lambda into the head would shadow a parameter of the same name — rename one of them" v);
                if List.mem v enclosing then
                  refuse (Printf.sprintf "hoisting the binder `%s` of the trailing lambda into the head would capture it by the destructuring pattern of a parameter it sits under — rename one of them" v))
              names;
            (* one arrow of the annotation per hoisted binder *)
            let typ_opt' =
              List.fold_left (fun (topt, ty) _ ->
                  let ty = Types.head_norm A.env.t_env ty in
                  match ty.Types.t with
                  | Types.Tfn (_, cod) -> (typ_after topt cod, cod)
                  | _ -> refuse "internal error — the trailing lambda binds more variables than its type has arrows")
                (typ_opt, Typed_ast.exp_to_typ e') ps |> fst in
            hoist (pats @ ps) typ_opt' body (enclosing) (hoisted @ names)
          | Case (b, cs1, scrut, cs2, arms, cs3) when Seplist.length arms = 1 ->
            (* the pattern compiler's destructuring match: its scrutinee is
               a parameter variable, or the tuple of several (`match p, p0
               with | (a, b), (c, d) => …` for two destructuring parameters) *)
            let is_param_var e0 = match C.exp_to_term (strip e0) with
              | Var v -> List.exists (fun q -> param_var q = Some (nm v)) pats
              | _ -> false in
            let on_params = match C.exp_to_term (strip scrut) with
              | Var _ -> is_param_var scrut
              | Tup (_, es, _) -> Seplist.to_list es <> [] && List.for_all is_param_var (Seplist.to_list es)
              | _ -> false in
            (match on_params, Seplist.to_list arms with
             | true, [(ap, as1, abody, al)] ->
               (match C.exp_to_term (strip abody) with
                | Fun _ ->
                  let (pats', typ_opt', abody', hoisted') =
                    hoist pats typ_opt abody (enclosing @ pat_names ap) hoisted in
                  if hoisted' == hoisted then (pats, typ_opt, e, hoisted)
                  else begin
                    let arms' = Seplist.map (fun (p0, s0, _, l0) -> (p0, s0, abody', l0)) arms in
                    let e'' = C.mk_case b (Typed_ast.exp_to_locn e') cs1 scrut cs2 arms' cs3
                        (Some (Typed_ast.exp_to_typ abody')) in
                    (pats', typ_opt', e'', hoisted')
                  end
                | _ -> (pats, typ_opt, e, hoisted))
             | _ -> (pats, typ_opt, e, hoisted))
          | _ -> (pats, typ_opt, e, hoisted) in
        let (pats', typ_opt', e', hoisted) = hoist pats typ_opt e [] [] in
        if hoisted = [] then g
        else begin
          if Types.Cdset.mem c !St.supply_lifted then
            refuse "eta-expansion of a supply-lifted definition (unsupported: the supply prepass threads call sites at the pre-hoist arity; extend when needed)";
          St.tail_hoisted := (c, hoisted) :: List.remove_assoc c !St.tail_hoisted;
          [(nla, c, pats', typ_opt', sk, e')]
        end
      | _ -> g
    (* Does this expression force fuel lifting of its enclosing def. *)
    let exp_needs_fuel (e : exp) : bool =
      let ue = add_exp_entities empty_used_entities e in
      List.exists (fun cref ->
          is_ambient_fuelled_cref cref || is_fuel_consumer_cref cref
          || Types.Cdset.mem cref !St.fuel_lifted)
        ue.used_consts
    (* The ambient-fuel binder: instance-implicit, so no call site
       changes — the ONE place the class name is spelled in a signature. *)
    let fuel_binder_output () =
      if !St.fuel_binder then from_string " [LemFuel]" else emp
    (* THE FAIL-CLOSED FUEL SCOPE NET: a fuel-lifted constant (or a
       fuel_consumer) rendered where no `[LemFuel]` binder is in scope
       would leave Lean to fail at build time ("failed to synthesize
       LemFuel") — or, worse, to pick up a stray global instance. There
       is no default to inject, by design: generation-time error naming
       the context. Inert for block comments (dead text). *)
    let fuel_scope_check (l : Ast.l) (cref : Types.const_descr_ref) (ctx : string) : unit =
      if not (!St.fuel_binder || !St.rendering_comment)
         && (Types.Cdset.mem cref !St.fuel_lifted || is_fuel_consumer_cref cref)
         (* a self/sibling call inside a fuel'd worker is rewritten to pass
            the decremented COUNTER (`(w lemFuel …)`), needing no instance *)
         && not (!St.fuel_emit <> None && List.mem_assoc cref !St.fuel_workers) then
        raise (Reporting_basic.err_general true l
          (Printf.sprintf
            "Lean backend: fuel'd (or fuel-lifted) definition referenced outside a fuel scope — %s — where no [LemFuel] instance is in scope (instance methods, indreln rules, lemmas/asserts cannot take the ambient fuel; fuel is a parameter of the semantics with no default: call the definition from a fuel-lifted definition, or from hand-written Lean that supplies the fuel, e.g. `@f ⟨n⟩ …` or `letI : LemFuel := ⟨n⟩`)"
            ctx))

    (* --- Instance-reader helpers (declare {lean} reader val r =
       instance `Cls.field`; the mechanism comment is at
       lean_ireader_projection). --- *)
    let is_ireader_cref = lean_ireader_is_reader A.env
    (* The read `r ()`: the class projection, resolved from the [Cls]
       binder in scope (ireader_scope_check has run at the site). *)
    let ireader_read_output cref =
      match lean_ireader_projection A.env cref with
      | Some proj ->
        (* the projection is target text, like a target_rep: its module
           prefix is imported by the same collector *)
        collect_cr_simple_import (is_library_module !St.current_module_name) proj;
        from_string proj
      | None ->
        raise (Reporting_basic.err_general true Ast.Unknown
          "Lean backend: internal error — instance-reader read of a constant with no projection")
    let ireader_class_of cref =
      match List.find_opt (fun (c, _, _) -> c = cref) (lean_ireader_get_readers A.env) with
      | Some (_, _, cls) -> cls
      | None ->
        raise (Reporting_basic.err_general true Ast.Unknown
          "Lean backend: internal error — instance-reader binder for a constant that is not an instance reader")
    (* The binders of a def group: the union of its members' lifted sets,
       in the global reader order. *)
    let ireader_group_binders (crefs : Types.const_descr_ref list) =
      if crefs = [] || lean_ireader_get_readers A.env = [] then []
      else lean_ireader_filter A.env (fun r ->
          List.exists (fun c -> List.mem r (lean_ireader_lifted_of c)) crefs)
    (* The instance-implicit binders: like `[LemFuel]`, no call site
       changes — the ONE place each class name is spelled in a signature. *)
    let ireader_binder_output () =
      Output.flat (List.map (fun r ->
          let cls = ireader_class_of r in
          collect_cr_simple_import (is_library_module !St.current_module_name) cls;
          Output.flat [from_string " ["; from_string cls; from_string "]"])
        !St.ireader_binder)
    (* THE FAIL-CLOSED INSTANCE-READER SCOPE NET: a read of an instance
       reader, or a reference to a member/consumer, rendered where its
       `[Cls]` binder is not in scope would leave Lean to fail at build
       time ("failed to synthesize Cls") — or, worse, to pick up a stray
       instance. There is no default to inject, by design: generation-time
       error naming the context and the missing classes. Inert for block
       comments (dead text). *)
    let ireader_scope_check (l : Ast.l) (cref : Types.const_descr_ref) (ctx : string) : unit =
      if not !St.rendering_comment then begin
        let missing = List.filter (fun r -> not (List.mem r !St.ireader_binder))
            (lean_ireader_needs A.env cref) in
        if missing <> [] then
          raise (Reporting_basic.err_general true l
            (Printf.sprintf
              "Lean backend: %s %s outside an instance-reader scope — %s — where no [%s] instance is in scope (instance methods, indreln rules, lemmas/asserts and other contexts the fixpoint cannot lift cannot bind it; the instance reader is a parameter with no default: read it from a definition the fixpoint lifts, or from hand-written Lean that supplies the instance, e.g. `@f ⟨v⟩ …` or `letI : Cls := ⟨v⟩`)"
              (if is_ireader_cref cref then "instance reader" else "definition reading the instance reader(s)")
              (lean_ireader_name A.env cref) ctx
              (String.concat "] [" (List.map ireader_class_of missing))))
      end

    (* --- Supply lifting helpers (declare {lean} supply val) ---
       thin wrappers over the top-level env-parameterized versions; the
       pre-pass lives at module-emission level (lean_supply_prepass).
       See the mechanism comment at lean_supply_is_supply. *)
    let is_supply_cref = lean_supply_is_supply A.env
    let get_supply_params () = lean_supply_get_params A.env
    let supply_arity_of cref =
      match Types.Cdmap.apply !St.supply_arity cref with
      | Some n -> n
      | None ->
        raise (Reporting_basic.err_general true Ast.Unknown
          "Lean backend: internal error — supply-lifted constant has no recorded threading arity")

    (* Does this expression force supply lifting of its enclosing def:
       a draw, or a call of an already-lifted def (transitive draws). *)
    let exp_needs_supply (e : exp) : bool =
      let ue = add_exp_entities empty_used_entities e in
      List.exists (fun cref ->
          is_supply_cref cref || Types.Cdset.mem cref !St.supply_lifted)
        ue.used_consts

    (* The zero-fuel arm's value: the declared sentinel; under supply
       lifting paired with the UNCONSUMED supply binders — fuel exhaustion
       draws nothing. Shared by the worker's `| 0 =>` arm and the
       generated `_zero` lemma, so the two agree by construction. *)
    let fuel_sentinel_output (sentinel : string) =
      if !St.supply_binder then
        Output.flat
          ([from_string "(("; from_string sentinel; from_string ")"]
           @ List.concat_map (fun (_, pname) ->
                 [from_string ", "; from_string pname])
               (get_supply_params ())
           @ [from_string ")"])
      else if !St.tail_sentinel_args <> [] then
        (* a hoisted `function` tail: the payload is written at the head's
           original (function) codomain — apply it to the hoisted binders
           (mechanism comment at lean_hoist_tail_binders) *)
        Output.flat
          ([from_string "(("; from_string sentinel; from_string ")"]
           @ List.concat_map (fun n -> [from_string " "; from_string (lean_escape_keyword n)])
               !St.tail_sentinel_args
           @ [from_string ")"])
      else Output.flat [from_string "("; from_string sentinel; from_string ")"]

    (* Short-circuit heads: lem constants
       whose Lean rep is the infix Bool operator && / ||. Lean's
       macro_inline and/or evaluate their RIGHT operand only on the
       non-short-circuit path, so the supply transform must thread a
       drawing right operand as a BRANCH ARM (a && b ≡ if a then b
       else false; a || b ≡ if a then true else b) — hoisting its
       draws above the test would consume supply the pre-transform
       code (and the OCaml oracle) does not. The LEFT operand stays
       strict (both references evaluate it). *)
    let lean_shortcircuit_kind (cref : Types.const_descr_ref) : string option =
      let cd = c_env_lookup Ast.Unknown A.env.c_env cref in
      match Target.Targetmap.apply_target cd.target_rep
              (Target.Target_no_ident Target.Target_lean) with
      | Some (CR_infix (_, _, _, i)) ->
        (match Ident.to_string i with
         | "&&" -> Some "&&"
         | "||" -> Some "||"
         | _ -> None)
      | _ -> None

    (* THE FAIL-CLOSED SUPPLY NET: ordinary (non-threaded) emission must
       never render a supply constant or a supply-lifted definition —
       there is no supply value in scope, and (unlike the reader's
       type-preserving partial application) no repair exists. Any such
       reach is a generation-time error naming the context: this is what
       makes guards G-bare / G-rel (indreln, lemma/assert) and the
       unliftable-context class structurally closed rather than
       Lean-build-time surprises. Suppressed only (a) while the supply
       transform itself renders a threaded call HEAD (St.supply_head_ok)
       and (b) inside block-comment renderings of dead text
       (St.rendering_comment: the checks are inert while dead text is
       rendered as a comment). *)
    let supply_net_check (l : Ast.l) (cref : Types.const_descr_ref) (ctx : string) : unit =
      if not (!St.supply_head_ok || !St.rendering_comment) then begin
        if is_supply_cref cref then
          raise (Reporting_basic.err_general true l
            (Printf.sprintf
              "Lean backend: supply constant used outside supply-threaded code (unsupported: a draw is only legal inside a definition body, which the pre-pass supply-lifts; in this context — %s — there is no supply to thread)"
              ctx))
        else if Types.Cdset.mem cref !St.supply_lifted then
          raise (Reporting_basic.err_general true l
            (Printf.sprintf
              "Lean backend: supply-lifted definition used outside supply-threaded code (unsupported: linear supply threading has no partial-application repair; context — %s)"
              ctx))
      end

    (* Fuel sentinel for the Lean target, if declared for this constant. *)
    let fuel_sentinel_for cref =
      let cd = c_env_lookup Ast.Unknown A.env.c_env cref in
      Target.Targetmap.apply_target cd.fuel_sentinel (Target.Target_no_ident Target.Target_lean)

    (* Ground-site alternative head (declare {lean} ground_rep val f =
       `Ident`): emitted instead of the constant at applications whose
       result type is syntactically ground. See the failwith special case
       below — same classification rule, declare-driven. *)
    let ground_rep_for cref =
      let cd = c_env_lookup Ast.Unknown A.env.c_env cref in
      Target.Targetmap.apply_target cd.ground_rep (Target.Target_no_ident Target.Target_lean)

    (* Constants whose LEAN target_rep is the bare identifier `failwith`
       (Assert_extra.failwith, cerberus's Utils.error, ...).
       EVERY such call site is re-emitted as LemLib.failwithI (opaque,
       [Inhabited]-bounded, axiom-free); tyvar-typed sites are
       discharged by the [Inhabited tv] binders the threading pre-pass
       put on the enclosing def (lean_failwith_thread_prepass). Legacy
       LemLib.failwith is never emitted. Shared with the pre-pass so
       the two can never disagree. *)
    let is_lean_failwith_rep cref = lean_is_failwith_rep_env A.env cref
    (* Rule-3 emission backstop (the pre-pass guard fires first with a
       better-named error): a failure site inside an instance method at
       a type not unconditionally discharged cannot be repaired by
       binder threading. *)
    let failwith_instance_guard inside_instance site_t =
      if inside_instance then
        match typ_inhabited_bounds A.env.t_env site_t with
        | Some [] -> ()
        | _ ->
          raise (Reporting_basic.err_general true Ast.Unknown
            "Lean backend: type-variable failure site inside a generated instance method — instance methods cannot carry [Inhabited] binders; escape hatches: give the method a Lean target_rep ('declare lean target_rep function ...') or restructure so the failure is at a concrete type")

    let rec def_extra (inside_instance: bool) (callback: def list -> Output.t) (inside_module: bool) (m: def_aux) =
      match m with
        | Lemma (skips, lemma_typ, targets, (name, _), skips', e) ->
          if in_target targets then
            let name_out = Name.to_output Term_var name in
            let name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name)) in
            match lemma_typ with
            | Ast.Lemma_assert _
              when exp_needs_fuel e && is_library_module !St.current_module_name ->
              (* A LIBRARY assert on a fuel-lifted definition (none today; it
                 arises the moment a library val is declared fuel_consumer —
                 measured on relation.lem's withoutTransitiveEdges rows while
                 that variant was built): there is no fuel to supply and the
                 library's auxiliary files are never built (`make lean-libs`
                 deletes them), so render the removal loudly instead of
                 failing the library build. A USER assert in the same
                 position is the fail-closed fuel_scope_check error
                 (negative/neg_fuel_scope_assert.lem). *)
              Output.flat [
                ws skips; from_string "/- lem: removed assert "; name_out;
                from_string ": it uses a fuel'd definition, and a library assert has no [LemFuel] instance to supply -/"
              ]
            | Ast.Lemma_assert _ ->
              Output.flat [
                ws skips;
                from_string "#eval do\n";
                from_string ("  if ("); exp inside_instance e; from_string (" : Bool)\n");
                from_string (String.concat "" ["  then IO.println \"PASS: "; lean_string_escape name_str; "\"\n"]);
                from_string (String.concat "" ["  else throw (IO.userError \"FAIL: "; lean_string_escape name_str; "\")"])
              ]
            | Ast.Lemma_lemma _ | Ast.Lemma_theorem _ ->
              (* A Lem lemma/theorem is emitted as a name marker only: its
                 statement is not translated (TODO item 29 considers emitting
                 the statement as a comment). *)
              Output.flat [
                ws skips; from_string "/- lem: theorem "; name_out; from_string " not translated -/"
              ]
          else
            from_string "/- lem: removed a lemma for another backend -/"
        (* All non-Lemma defs are handled by def, not def_extra.
           Exhaustive match so new def_aux variants trigger a compiler warning. *)
        | Type_def _ | Val_def _ | Module _ | Rename _ | OpenImport _
        | OpenImportTarget _ | Indreln _ | Val_spec _ | Class _ | Instance _
        | Comment _ | Declaration _ -> emp
    and def (inside_instance: bool) (callback : def list -> Output.t) (inside_module : bool) (m : def_aux) =
      match m with
      | Type_def (skips, def) ->
          lean_check_type_block def;
          let type_output =
            if Seplist.length def = 1 then
              match Seplist.hd def with
              | ((n, _), tyvars, path, Te_abbrev (sk, t), _) ->
                  type_def_abbreviation n tyvars path sk t
              | (n, tyvars, path, (Te_record (_, _, fields, _) as ty), _) ->
                  type_def_record n tyvars path ty fields
              | _ -> type_def inside_module def
            else
              type_def inside_module def
          in
          let defaults =
            if Seplist.length def > 1 then
              generate_default_values_mutual def
            else
              generate_default_values def
          in
            Output.flat [
              ws skips; type_output;
              defaults;
            ]
      | Val_def (def) ->
          let class_constraints = val_def_get_class_constraints A.env def in
          let tv_set = val_def_get_free_tnvars A.env def in
          let (_, is_real_rec, try_term) =
            Typed_ast_syntax.try_termination_proof
              (Target_no_ident Target_lean) A.env.c_env m
          in
          val_def false None is_real_rec try_term def tv_set class_constraints
      | Module (skips, (name, l), mod_binding, skips', skips'', defs, skips''') ->
        let name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name)) in
        St.local_modules := name_str :: !St.local_modules;
        St.namespace_stack := name_str :: !St.namespace_stack;
        (* Build fully-qualified path for this module *)
        let fq_path = String.concat "." (List.rev !St.namespace_stack) in
        let name = lskips_t_to_output name in
        let body = Fun.protect ~finally:(fun () ->
          St.namespace_stack := (match !St.namespace_stack with _ :: tl -> tl | [] -> [])
        ) (fun () -> callback defs) in
          (* In Lem, module contents are implicitly available after the module
             definition. Lean namespaces are not — we need an explicit 'open'.
             For top-level modules, emit 'open' directly plus any deferred
             opens from nested modules. For nested modules, defer the open
             since Lean's 'open' inside a namespace is scoped to that block. *)
          let is_top_level = !St.namespace_stack = [] in
          if is_top_level then
            let deferred = !St.deferred_opens in
            St.deferred_opens := [];
            let deferred_opens = flat @@ List.map (fun p ->
              from_string (String.concat "" ["\nopen "; p])
            ) deferred in
            Output.flat [
              ws skips; from_string "namespace "; name; ws skips'; ws skips'';
              body; from_string "\nend "; name;
              from_string "\nopen "; name; deferred_opens; ws skips'''
            ]
          else begin
            St.deferred_opens := fq_path :: !St.deferred_opens;
            Output.flat [
              ws skips; from_string "namespace "; name; ws skips'; ws skips'';
              body; from_string "\nend "; name;
              from_string "\nopen "; name; ws skips'''
            ]
          end
      | Rename (skips, name, mod_binding, skips', mod_descr) -> emp  (* Module renames not applicable in Lean *)
      | OpenImport (oi, ms) ->
          let (ms', sk) = B.open_to_open_target ms in
          if (ms' = []) then
             ws (oi_get_lskip oi)
          else (
            let d' = OpenImportTarget(oi, Targets_opt_none, ms') in
            def inside_instance callback inside_module d' ^ ws sk
          )
      | OpenImportTarget(oi, _, []) -> ws (oi_get_lskip oi)
      | OpenImportTarget (Ast.OI_open skips, targets, mod_descrs) ->
          ws skips ^
          let is_user_module = not (is_library_module !St.current_module_name) in
          let handle_mod (sk, md) =
            (if not (List.mem md !St.local_modules) then
              St.collected_imports := md :: !St.collected_imports);
            (* Emit 'open' for:
               - Local modules (defined in this file via Module) — they create namespaces
               - Library modules in library context — they have Lem_X namespaces
               User modules from other files have no namespace; import alone suffices.
               In non-library (user) modules, skip inline opens for library imports —
               transitive_opens will emit them for both main and auxiliary files. *)
            if List.mem md !St.local_modules then
              Output.flat [
                from_string "open"; ws sk; from_string md; from_string "\n"
              ]
            else if not (is_library_module md) then emp
            else if is_user_module then emp
            else
              let ns = lean_ns_name md in
              Output.flat [
                from_string "open"; ws sk; from_string ns; from_string "\n"
              ]
          in
          if (not (in_target targets)) then emp else Output.flat (List.map handle_mod mod_descrs)
      | OpenImportTarget _ ->
          (* Unreachable: def_trans converts all OI variants to OI_open *)
          raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected non-OI_open OpenImportTarget")
      | Indreln (skips, targets, names, cs) ->
          if in_target targets then
            let c = Seplist.to_list cs in
              clauses inside_instance c
          else
            ws skips ^ from_string "\n/- lem: removed an inductive relation for another backend -/"
      | Val_spec (_, (n, _), _, _, s2, (_, t)) ->
          (* No Lean counterpart (the def carries the type); its comments
             stay: those in front of it, then those inside its type, one
             per line. *)
          let inner = List.concat_map (fun sk -> let (a, b) = split_skip_comments sk in a @ b)
              (Name.get_lskip n :: s2 :: src_t_skips t) in
          Output.flat [init_comments m; leading_comments ~indent:"" inner]
      | Class (Ast.Class_inline_decl (skips, _), _, _, _, _,_, _, _) -> ws skips
      | Class (Ast.Class_decl skips, skips', (name, l), tv, p, skips'', body, skips''') ->
          let name_str = Name.to_string (B.class_path_to_name p) in
          St.auxiliary_opens := lean_qualified_name name_str :: !St.auxiliary_opens;
          let name = from_string name_str in
          let tv_kind = tnvar_kind tv in
          let tv = from_string (tnvar_to_string tv) in
          let method_names = ref [] in
          let body_entries =
            List.filter_map (fun (skips, targets_opt, (name, l), const_descr_ref, ascii_rep_opt, skips', src_t) ->
              if in_target targets_opt then
                let name' = B.const_ref_to_name name true const_descr_ref in
                let name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name')) in
                  method_names := name_str :: !method_names;
                  Some (Output.flat [
                    ws skips; from_string name_str; from_string " :"; ws skips'; pat_typ src_t
                  ])
              else
                None
            ) body
          in
          let body_out = Output.concat (from_string "\n") body_entries in
          (* If the class has an isEqual method (i.e., this is Lem's Eq class),
             emit a BEq bridge instance so that == works wherever [Eq0 a] is available.
             This is needed because isEqual is mapped to == (BEq) in Lean. *)
          let has_isEqual = List.exists (fun (_, _, (mn, _), cref, _, _, _) ->
            (* Check if any method has target_rep mapped to == (BEq).
               The method's original name might be = with isEqual as alternative,
               so check the const_descr for the Lean target rep. *)
            let cd = c_env_lookup Ast.Unknown A.env.c_env cref in
            match Target.Targetmap.apply_target cd.target_rep
                    (Target.Target_no_ident Target.Target_lean) with
            | Some (CR_infix(_, _, _, op_id)) ->
                Ident.to_string op_id = "=="
            | _ -> false
          ) body in
          (* Check if the class has a comparison method (returns LemOrdering).
             Known: setElemCompare (SetType), mapKeyCompare (MapKeyType).
             If so, derive BEq from the comparison function. *)
          let compare_method_names = ["setElemCompare"; "mapKeyCompare"] in
          let compare_method = List.find_opt (fun n ->
            List.mem n compare_method_names
          ) (List.rev !method_names) in
          let beq_bridge =
            if has_isEqual then
              (* The isEqual bridge ([Eq0 a] : BEq a) sits BELOW core's
                 `[DecidableEq a] : BEq a` (500), so `==` at a base type is
                 core's structural equality and a model Eq0 still gives `==`
                 to a type that has no other BEq; and ABOVE the comparator
                 bridge below (lean_instance_eq0_bridge_priority). *)
              Output.flat [
                from_string (String.concat "" [lean_instance_kw lean_instance_eq0_bridge_priority; " {"]);
                tv; from_string " : "; from_string tv_kind;
                from_string "} ["; name; from_string " "; tv; from_string "] : BEq "; tv;
                from_string " where\n  beq := isEqual\n"
              ]
            else match compare_method with
            | Some cmp_name ->
              (* The comparator-derived BEq bridge ([SetType a]/[MapKeyType a]
                 : BEq a) sits strictly BELOW the isEqual bridge, derived BEq
                 (default = 1000) and core's BEq (500): a comparator can be
                 COARSER than a type's own equality, so when both apply the
                 finer Eq0 route must win by PRIORITY, not by declaration
                 order (lean_instance_comparator_bridge_priority). *)
              Output.flat [
                from_string (String.concat "" [lean_instance_kw lean_instance_comparator_bridge_priority; " {"]);
                tv; from_string " : "; from_string tv_kind;
                from_string "} ["; name; from_string " "; tv; from_string "] : BEq "; tv;
                from_string (String.concat "" [" where\n  beq x y := match "; cmp_name; " x y with | .EQ => true | _ => false\n"])
              ]
            | None -> emp
          in
          (* Export class methods so they are visible to importing files.
             Skip names that clash with Lean stdlib globals — a clash here
             causes a Lean compile error (ambiguous name), not silent failure.
             Review this list when upgrading the Lean toolchain. *)
          let lean_global_names = ["max"; "min"; "compare"] in
          let exportable = List.filter (fun n ->
            not (List.mem n lean_global_names)
          ) (List.rev !method_names) in
          let class_export =
            if exportable = [] then
              Output.flat [from_string "\nopen "; name; from_string "\n"]
            else begin
              let names_str = String.concat "" ["("; String.concat " " exportable; ")"] in
              Output.flat [
                from_string "\nexport "; name; from_string " "; from_string names_str; from_string "\n"
              ]
            end
          in
          Output.flat [
            ws skips; from_string "class"; ws skips'; name; from_string " ("; tv; from_string " : "; from_string tv_kind; from_string ") where"
          ; ws skips''; from_string "\n"; body_out
          ; ws skips'''; from_string "\n"; class_export
          ; beq_bridge
          ]
      | Instance ((Ast.Inst_default skips | Ast.Inst_decl skips) as inst_kind, i_ref, inst, vals, skips') ->
        let is_default = match inst_kind with Ast.Inst_default _ -> true | _ -> false in
        (* Filter out instance methods whose corresponding class methods
           are not visible for the Lean target *)
        let instance_info = Types.i_env_lookup Ast.Unknown A.env.i_env i_ref in
        let class_method_visible (inst_cd_ref : Types.const_descr_ref) : bool =
          let found = List.filter (fun (_, inst_ref) -> inst_ref = inst_cd_ref) instance_info.inst_methods in
          match found with
          | (class_ref, _) :: _ ->
            let class_cd = c_env_lookup Ast.Unknown A.env.c_env class_ref in
            Typed_ast.in_target_set (Target.Target_no_ident Target.Target_lean) class_cd.const_targets
          | [] ->
            raise (Reporting_basic.err_general true Ast.Unknown
              "Lean backend: instance method has no corresponding class method in inst_methods")
        in
        let val_is_visible (d : Typed_ast.val_def) : bool =
          match d with
          | Let_def (_, _, (_, name_map, _, _, _)) ->
            List.for_all (fun (_, cd_ref) -> class_method_visible cd_ref) name_map
          | Fun_def (_, _, _, funcl_sep) ->
            Seplist.for_all (fun ({term = _}, c, _, _, _, _) -> class_method_visible c) funcl_sep
          | Let_inline _ ->
            raise (Reporting_basic.err_general true Ast.Unknown
              "Lean backend: unexpected Let_inline in instance body")
        in
        let vals = List.filter val_is_visible vals in
          let prefix =
            match inst with
              | (constraint_prefix_opt, skips, ident, path, src_t, skips') ->
                let tnvar_list_opt, tyvars, c =
                  begin
                  match constraint_prefix_opt with
                    | None -> None, emp, emp
                    | Some c ->
                      begin
                      match c with
                        | Cp_forall (skips, tnvar_list, skips', constraints_opt) ->
                            let tnvars =
                              Output.concat (from_string " ") (List.map (fun t ->
                                match t with
                                  | Typed_ast.Tn_A (_, var, _) ->
                                      from_string @@ Ulib.Text.to_string var
                                  | Typed_ast.Tn_N (_, var, _) ->
                                      from_string @@ Ulib.Text.to_string var
                              ) tnvar_list)
                            in
                            (* Use fully qualified paths from the type system
                               rather than parsing unqualified Idents from the AST.
                               The Cs_list Idents may be unqualified (e.g., "Eq"
                               instead of "Basic_classes.Eq"), which fails to look
                               up in t_env for class renaming. *)
                            let cs =
                              Output.concat (from_string " ") (List.map (fun (cpath, tnvar) ->
                                let class_name = B.class_path_to_name cpath in
                                let var = from_string @@ Ulib.Text.to_string @@ Types.tnvar_to_rope tnvar in
                                Output.flat [
                                  from_string "["; from_string (Name.to_string class_name);
                                  from_string " "; var; from_string "]"
                                ]
                              ) instance_info.Types.inst_constraints)
                            in
                            (* Add extra constraints from TYR_subst type target reps *)
                            let extra_tyr = extra_constraints_for_tyr_subst instance_info.Types.inst_type in
                            let new_extras = filter_new_tyr_constraints extra_tyr instance_info.Types.inst_constraints in
                            let cs = cs ^ format_tyr_constraints new_extras in
                            (* Add Lean-native constraints for default instances *)
                            let cs =
                              if is_default then
                                let target_class = Name.to_string (B.class_path_to_name path) in
                                let extra_classes = lean_default_instance_extra_constraints target_class in
                                let pairs = List.concat_map (fun cls ->
                                  List.filter_map (fun t ->
                                    match t with
                                    | Typed_ast.Tn_A (_, var, _) ->
                                      Some (cls, Ulib.Text.to_string var)
                                    | _ -> None
                                  ) tnvar_list
                                ) extra_classes in
                                cs ^ format_tyr_constraints pairs
                              else cs
                            in
                              Some tnvar_list, tnvars, cs
                      end
                  end
                in
                let id = from_string (Name.to_string (B.class_path_to_name path)) in
                let tyvars_typeset =
                  if tyvars = emp then
                    emp
                  else
                    match tnvar_list_opt with
                    | Some tnvar_list ->
                      let has_nvar = List.exists (fun t ->
                        match t with Typed_ast.Tn_N _ -> true | _ -> false) tnvar_list in
                      if has_nvar then
                        Output.concat (from_string " ") (List.map (fun t ->
                          match t with
                            | Typed_ast.Tn_A (_, var, _) ->
                              Output.flat [from_string "("; from_string @@ Ulib.Text.to_string var; from_string " : Type)"]
                            | Typed_ast.Tn_N (_, var, _) ->
                              Output.flat [from_string "("; from_string @@ Ulib.Text.to_string var; from_string " : Nat)"]
                        ) tnvar_list)
                      else
                        Output.flat [
                          from_string "("; tyvars; from_string " : Type)"
                        ]
                    | None ->
                      Output.flat [
                        from_string "("; tyvars; from_string " : Type)"
                      ]
                in
                  (* Wrap the class type argument in parens if it's a type application
                     (e.g., mem_constraint a → (mem_constraint a)). Without this,
                     Lean parses 'Constraints mem_constraint a' as two arguments. *)
                  let type_arg = match src_t.term with
                    | Typ_app (_, _ :: _) ->
                      Output.flat [from_string " ("; pat_typ src_t; from_string ")"]
                    | _ -> pat_typ src_t
                  in
                  Output.flat [
                    ws skips; tyvars_typeset; from_string " "; c; from_string " : "; id
                  ; type_arg
                  ]
          in
          let body =
            Output.concat (from_string "\n") (List.map (fun d -> val_def true (Some i_ref) false true d Types.TNset.empty []) vals)
          in
            let inst_kw = if is_default
              then from_string "instance (priority := low)"
              else if lean_tuple_inst_named A.env instance_info
              then from_string (Stdlib.(^) "instance _root_." (lean_tuple_inst_name A.env instance_info))
              else from_string "instance" in
            Output.flat [
              ws skips; inst_kw; prefix; from_string " where";
              from_string "\n"; body;
              ws skips'
            ]
      | Comment c ->
        let ((def_aux, skips_opt), l, lenv) = c in
        let skips = match skips_opt with None -> from_string "\n" | Some s -> ws s in
        (* Check if this is a Type_def with a TYR_subst target rep for Lean.
           If so, emit an abbrev definition instead of just a block comment.
           This enables parameterized type mappings like mword 'a → BitVec (Size.size a). *)
        let abbrev_for_target_rep = match def_aux with
          | Type_def (_, sl) when Seplist.length sl = 1 ->
            let ((n0, _), tyvars, t_path, _, _) = Seplist.hd sl in
            let td = Types.type_defs_lookup l A.env.t_env t_path in
            begin match Target.Targetmap.apply_target td.Types.type_target_rep
                    (Target.Target_no_ident Target.Target_lean) with
            | Some (Types.TYR_subst (_, _, _, rhs_t)) ->
              let name = B.type_path_to_name n0 t_path in
              let name_out = Name.to_output (Type_ctor (false, false)) name in
              let tyvars_out = type_def_type_variables tyvars in
              let rhs_out = pat_typ rhs_t in
              let class_constraints = collect_class_constraints_from_src_t rhs_t in
              let constraints_out = Output.flat (List.map (fun (cls, tv) ->
                Output.flat [from_string "["; from_string cls; from_string " "; from_string tv; from_string "] "]
              ) class_constraints) in
              Some (Output.flat [
                from_string "\nabbrev "; name_out; from_string " "; tyvars_out;
                constraints_out;
                from_string " := "; rhs_out; from_string "\n"
              ])
            | _ -> None
            end
          | _ -> None
        in
        let comment =
          let saved = !St.rendering_comment in
          St.rendering_comment := true;
          Fun.protect ~finally:(fun () -> St.rendering_comment := saved) @@ fun () ->
          Output.flat [
            skips; from_string "/- lem: replaced by its target representation: "; def inside_instance callback inside_module def_aux; from_string " -/"
          ] in
        begin match abbrev_for_target_rep with
        | Some abbrev_out ->
          St.pending_abbrevs := abbrev_out :: !St.pending_abbrevs;
          comment
        | None -> comment
        end
      | Declaration (Decl_extra_import (_, _, _, _, mod_name)) ->
          (* Add user-requested import to this file's import list *)
          if not (List.mem mod_name !St.collected_imports) then
            St.collected_imports := mod_name :: !St.collected_imports;
          init_comments m
      | Declaration _ -> init_comments m  (* processed earlier; its comments stay *)
      | Lemma _ -> emp  (* Lemmas are handled by def_extra, not def *)
    and val_def inside_instance i_ref_opt is_recursive try_term def tv_set class_constraints =
      (* type-variable renames for this definition (lean_tyvar_renames_for) *)
      let renames =
        if inside_instance || !St.rendering_comment then [] else
        let (pats, exps) = match def with
          | Let_def (_, _, (p, _, _, _, e)) -> ([p], [e])
          | Fun_def (_, _, _, funs) ->
            List.fold_left (fun (ps, es) ((_, _, pats, _, _, e) : funcl_aux) -> (ps @ pats, es @ [e]))
              ([], []) (Seplist.to_list funs)
          | Let_inline (_, _, _, _, _, _, _, e) -> ([], [e]) in
        lean_tyvar_renames_for A.env tv_set pats exps in
      let saved = !St.tyvar_renames in
      St.tyvar_renames := renames;
      Fun.protect ~finally:(fun () -> St.tyvar_renames := saved) @@ fun () ->
      val_def_rendered inside_instance i_ref_opt is_recursive try_term def tv_set class_constraints
    and val_def_rendered inside_instance i_ref_opt is_recursive try_term def tv_set class_constraints =
      begin
        let constraints =
          let body =
            Output.concat (from_string " ") (List.map (fun (path, tnvar) ->
              let name = from_string (Name.to_string (B.class_path_to_name path)) in
              let var = from_string (lean_tyvar_text (Ulib.Text.to_string (Types.tnvar_to_rope tnvar)))
              in
                Output.flat [
                  from_string "["; name; from_string " "; var; from_string "]"
                ]
            ) class_constraints)
          in
          (* Collect extra constraints introduced by TYR_subst type target reps.
             For example, mword 'a → BitVec (@Size.size 'a _) introduces [Size 'a].
             Skip when inside_instance — the instance header already has the constraint. *)
          let extra_tyr = if inside_instance then [] else
            let l_unk = Ast.Trans (true, "lean_tyr_extra", None) in
            let cs = match def with
              | Let_def(_, _, (_, nm, _, _, _)) -> List.map snd nm
              | Let_inline(_,_,_,_,c,_,_,_) -> [c]
              | Fun_def(_, _, _, funs) ->
                Seplist.to_list_map (fun ((_, c, _, _, _, _):funcl_aux) -> c) funs
            in
            let cds = List.map (c_env_lookup l_unk A.env.c_env) cs in
            let extras = List.concat_map (fun cd ->
              extra_constraints_for_tyr_subst cd.const_type
            ) cds in
            filter_new_tyr_constraints extras class_constraints
          in
          (* comparison dictionaries (lean_cmp_prepass) *)
          let cmp_binders = if inside_instance then [] else
            let cs = match def with
              | Let_def(_, _, (_, nm, _, _, _)) -> List.map snd nm
              | Let_inline(_,_,_,_,c,_,_,_) -> [c]
              | Fun_def(_, _, _, funs) ->
                Seplist.to_list_map (fun ((_, c, _, _, _, _):funcl_aux) -> c) funs in
            List.fold_left (fun acc c ->
              List.fold_left (fun acc b -> if List.mem b acc then acc else acc @ [b]) acc
                (Option.value ~default:[] (Hashtbl.find_opt St.lean_cmp_bounds c))) [] cs in
          let cmp_out = Output.concat (from_string " ") (List.map (fun (cls, a) ->
            from_string (Printf.sprintf "[%s %s]" cls (lean_tyvar_text a))) cmp_binders) in
          let base =
            if List.length class_constraints = 0 && extra_tyr = [] then emp
            else body ^ format_tyr_constraints extra_tyr in
          if cmp_binders = [] then base
          else if base = emp then cmp_out
          else Output.flat [base; from_string " "; cmp_out]
        in
        match def with
          | Let_def (skips, targets, (p, name_map, topt, sk, e)) ->
              if in_target targets then
                (* Lean doesn't support destructuring in 'def' bindings.
                   Emit one def per bound name: def x : T := let PAT := EXPR; x *)
                let pat_out = def_pattern p in
                let type_out = match topt with
                  | None -> emp
                  | Some (_, t) -> Output.flat [from_string " :"; pat_typ t]
                in
                let let_lifted =
                  let lifted = List.exists (fun (_, cref) ->
                      Types.Cdset.mem cref !St.reader_lifted) name_map in
                  if exp_needs_reader e && inside_instance then
                    raise (Reporting_basic.err_general true Ast.Unknown
                      "Lean backend: reader-lifted call inside an instance method (unsupported: instance fields cannot take extra parameters)");
                  lifted && not inside_instance in
                (* Fuel lifting on a Let_def-bound constant: the bound name
                   takes the `[LemFuel]` binder like any lifted def. *)
                let let_fuel_lifted =
                  let lifted =
                    (not !St.rendering_comment)
                    && List.exists (fun (_, cref) ->
                           Types.Cdset.mem cref !St.fuel_lifted) name_map in
                  if (not !St.rendering_comment) && exp_needs_fuel e && inside_instance then
                    raise (Reporting_basic.err_general true Ast.Unknown
                      "Lean backend: fuel'd (or fuel-lifted) call inside an instance method (unsupported: instance fields cannot take the [LemFuel] binder)");
                  lifted && not inside_instance in
                (* Supply lifting on a Let_def-bound constant: the bound
                   name becomes a function of the supply (state-passing
                   semantics of a drawing value binding — each use
                   threads; documented in the feature doc). G-inst as
                   for Fun_defs; inert for block comments. *)
                let supply_let_lifted =
                  let lifted =
                    (not !St.rendering_comment)
                    && List.exists (fun (_, cref) ->
                           Types.Cdset.mem cref !St.supply_lifted) name_map in
                  if (not !St.rendering_comment) && exp_needs_supply e && inside_instance then
                    raise (Reporting_basic.err_general true Ast.Unknown
                      "Lean backend: supply draw (or supply-lifted call) inside an instance method (unsupported: instance fields cannot take extra parameters or change their result type)");
                  lifted && not inside_instance in
                let saved_reader_binder = !St.reader_binder in
                let saved_supply_binder = !St.supply_binder in
                let saved_fuel_binder = !St.fuel_binder in
                let saved_ireader_binder = !St.ireader_binder in
                St.reader_binder := let_lifted;
                St.supply_binder := supply_let_lifted;
                St.fuel_binder := let_fuel_lifted;
                (* instance readers: the bound names' lifted set (inside an
                   instance there is no binder — a read there is the
                   ireader_scope_check error) *)
                St.ireader_binder :=
                  (if inside_instance || !St.rendering_comment then []
                   else ireader_group_binders (List.map snd name_map));
                Fun.protect ~finally:(fun () ->
                    St.reader_binder := saved_reader_binder;
                    St.supply_binder := saved_supply_binder;
                    St.fuel_binder := saved_fuel_binder;
                    St.ireader_binder := saved_ireader_binder) @@ fun () ->
                let exp_out =
                  if supply_let_lifted then supply_block inside_instance e
                  else exp inside_instance e in
                let lean_name_of cref =
                  let cd = c_env_lookup Ast.Unknown A.env.c_env cref in
                  let (_, renamed, _) = Typed_ast_syntax.constant_descr_to_name
                    (Target.Target_no_ident Target.Target_lean) cd in
                  let s = Name.to_string renamed in
                  lean_check_reserved_def_name (exp_to_locn e) s; s in
                (* [Inhabited tv] binders for a threaded Let_def-bound
                   constant. *)
                let thread_out_of cref =
                  if inside_instance then emp
                  else match lean_thread_lookup cref with
                    | Some (_, ns) ->
                      Output.flat (List.map (fun n ->
                          Output.flat [from_string " [Inhabited "; from_string n; from_string "]"]) ns)
                    | None -> emp in
                (* A multi-name
                   destructuring let must NOT duplicate its RHS per bound
                   name — OCaml evaluates the RHS once, so a duplicated
                   supply-drawing (or hand-written-impure-extern) RHS is a
                   silent divergence. Multi-name lets emit ONE private
                   RHS def plus per-name projections; single-name lets
                   keep the historical shape byte-for-byte. A user val
                   colliding with the synthesized 'lemLetRhs_*' name
                   fails loudly at Lean compile time (duplicate def). *)
                let rhs_binding = match name_map with
                  | [] | [_] -> None
                  | _ ->
                    let rhs_def_name =
                      String.concat "" ["lemLetRhs_"; String.concat "_"
                        (List.map (fun (_, cref) -> lean_name_of cref) name_map)] in
                    (* the pre-pass records ONE demand for the whole
                       Let_def, so every cref carries the same
                       [Inhabited] set — take the first *)
                    let rhs_thread = (match name_map with
                      | (_, cref0) :: _ -> thread_out_of cref0
                      | [] -> emp) in
                    let rhs_typ =
                      let base = pat_typ (C.t_to_src_t (Typed_ast.exp_to_typ e)) in
                      if supply_let_lifted then
                        Output.flat [from_string "(("; base; from_string ")";
                                     supply_pair_suffix (); from_string ")"]
                      else base in
                    Some (rhs_def_name, Output.flat [
                      from_string "\n";
                      from_string "private def "; from_string rhs_def_name;
                      fuel_binder_output (); ireader_binder_output (); reader_binder_output (); supply_binder_output (); constraints; rhs_thread;
                      from_string "  : "; rhs_typ;
                      from_string " :="; exp_out
                    ]) in
                let body_out = match rhs_binding with
                  | None -> exp_out
                  | Some (rhs_def_name, _) ->
                    (* re-inject the reader parameters when lifted, and
                       thread the supply binders when supply-lifted: the
                       projections carry the same binders as the RHS def
                       (ONE call of the single-RHS def per projection —
                       the single-evaluation emitter; a duplicated
                       RHS would fork the draw numbering) *)
                    Output.flat [from_string " "; from_string rhs_def_name;
                                 (if let_lifted then reader_args_output () else emp);
                                 (if supply_let_lifted then
                                    Output.flat (List.map (fun (_, pname) ->
                                        Output.flat [from_string " "; from_string pname])
                                      (get_supply_params ()))
                                  else emp)] in
                let defs = List.map (fun (_orig_name, cref) ->
                  let cd = c_env_lookup Ast.Unknown A.env.c_env cref in
                  let name_str = lean_name_of cref in
                  let var_type = pat_typ (C.t_to_src_t cd.const_type) in
                  let defn = if inside_instance then emp else from_string "def " in
                  let thread_out = thread_out_of cref in
                  if supply_let_lifted then begin
                    (* threaded shape: bind the RHS pair, return the
                       bound name paired with the final supply *)
                    let states = List.map (fun _ -> supply_fresh_name "S")
                        (get_supply_params ()) in
                    let states_out = Output.flat (List.concat_map (fun s ->
                        [from_string ", "; from_string s]) states) in
                    Output.flat [
                      from_string "\n"; defn; from_string name_str;
                      fuel_binder_output (); ireader_binder_output (); reader_binder_output (); supply_binder_output (); constraints; thread_out;
                      from_string "  : (("; var_type; from_string ")";
                      supply_pair_suffix (); from_string ")";
                      from_string " :=\n  let (("; pat_out; type_out; from_string ")";
                      states_out; from_string ")"; ws sk; from_string " := (";
                      body_out; from_string ")";
                      from_string "\n  ("; from_string name_str; states_out; from_string ")"
                    ]
                  end else
                  Output.flat [
                    from_string "\n"; defn; from_string name_str;
                    fuel_binder_output (); ireader_binder_output (); reader_binder_output (); constraints; thread_out;
                    from_string "  : "; var_type;
                    from_string " :=\n  let "; pat_out; type_out;
                    ws sk; from_string " :="; body_out;
                    from_string "\n  "; from_string name_str
                  ]
                ) name_map in
                let defs = match rhs_binding with
                  | None -> defs
                  | Some (_, rhs_def) -> rhs_def :: defs in
                Output.flat (ws skips :: defs)
              else
                ws skips ^ from_string "/- lem: removed a definition for another backend -/"
          | Fun_def (skips, rec_flag, targets, funcl_skips_seplist) ->
              if in_target targets then
                let skips' = match rec_flag with FR_non_rec -> None | FR_rec sk -> sk in
                let funcls = Seplist.to_list funcl_skips_seplist in
                (* Group clauses by their defined constant, preserving
                   definition order — the shared cref-keyed grouping
                   (lean_group_funcls), same traversal as the
                   failwith-thread pre-pass. Multi-clause groups render
                   as Lean 4 pattern-matching equations. *)
                let groups = List.map snd (lean_group_funcls funcls) in
                (* point-free `function` tails of measured/structural
                   members (mechanism comment at lean_hoist_tail_binders):
                   hoisted BEFORE every analysis below reads the clause
                   parameters *)
                let groups = List.map (lean_hoist_tail_binders inside_instance) groups in
                let num_functions = List.length groups in
                (* Acyclic de-mutualization: a 'let rec ... and ...'
                   block whose call graph is a DAG (ignoring self-loops) is
                   emitted as SEQUENTIAL defs in dependency order — Lean's
                   'mutual' is reserved for genuine cycles. Lem sources use
                   rec-and chains freely for non-mutual defs; keeping them
                   mutual both blocks per-member termination handling and
                   forces fuel onto members that are not even recursive. *)
                let group_cref g = match g with
                  | (_, c, _, _, _, _) :: _ -> Some c
                  | [] -> None in
                let group_used g =
                  List.fold_left (fun acc (_, _, _, _, _, e) ->
                      let ue = add_exp_entities empty_used_entities e in
                      ue.used_consts @ acc) [] g in
                let group_self_recursive g = match group_cref g with
                  | Some c -> List.mem c (group_used g)
                  | None -> false in
                let demutualized =
                  if num_functions <= 1 then None
                  else begin
                    let arr = Array.of_list groups in
                    let n = Array.length arr in
                    let uses = Array.map group_used arr in
                    let dep i j =
                      i <> j
                      && (match group_cref arr.(j) with
                          | Some cj -> List.mem cj uses.(i)
                          | None -> false) in
                    (* Kahn's algorithm, stable: each round emits (in
                       original order) every def whose dependencies are all
                       emitted. No progress with nodes left = a cycle. *)
                    let emitted = Array.make n false in
                    let result = ref [] in
                    let count = ref 0 in
                    let progress = ref true in
                    while !count < n && !progress do
                      progress := false;
                      for i = 0 to n - 1 do
                        if not emitted.(i) then begin
                          let ready = ref true in
                          for j = 0 to n - 1 do
                            if (not emitted.(j)) && dep i j then ready := false
                          done;
                          if !ready then begin
                            emitted.(i) <- true;
                            result := arr.(i) :: !result;
                            incr count;
                            progress := true
                          end
                        end
                      done
                    done;
                    if !count = n then Some (List.rev !result) else None
                  end in
                let groups, is_truly_mutual = match demutualized with
                  | Some sorted -> sorted, false
                  | None -> groups, num_functions > 1 in
                let auto_term_for g = match group_cref g with
                  | Some c ->
                    let cd = c_env_lookup Ast.Unknown A.env.c_env c in
                    (match Target.Targetmap.apply_target cd.termination_setting
                             (Target.Target_no_ident Target.Target_lean) with
                     | Some (Ast.Termination_setting_automatic _) -> true
                     | _ -> false)
                  | None -> false in
                (* declare {lean} structural val: ordinary `def` +
                   `termination_by structural <param>` (mechanism comment
                   at lean_is_structural). Guards, fail-closed: not inside
                   an instance (a method has no def keyword or clause to
                   attach to), single-clause only (the equation-compiler
                   form has no named parameter to designate), and never
                   inert — the definition must actually recurse; in a truly
                   mutual block every member carries the declare (all-or-
                   none, as for fuel: Lean's mutual structural recursion
                   needs a clause on each). Inert while rendering block
                   comments (dead text). *)
                let structural_for g = match group_cref g with
                  | Some c -> is_structural_cref c
                  | None -> false in
                let any_structural =
                  (not !St.rendering_comment) && List.exists structural_for groups in
                if any_structural then begin
                  List.iter (fun g ->
                      if structural_for g then begin
                        if inside_instance then
                          raise (Reporting_basic.err_general true (locn_of_clause_group g)
                            "Lean backend: 'declare {lean} structural val' inside an instance (unsupported: define the recursion at top level and reference it from the instance method)");
                        if List.length g > 1 then
                          raise (Reporting_basic.err_general true (locn_of_clause_group g)
                            "Lean backend: 'declare {lean} structural val' on a multi-clause definition (unsupported; write the clauses as a single match so the structural parameter has a name)");
                        if not is_truly_mutual && not (group_self_recursive g) then
                          raise (Reporting_basic.err_general true (locn_of_clause_group g)
                            "Lean backend: 'declare {lean} structural val' on a definition that is not recursive (ST-nonrec: the declare would be inert — a non-recursive definition is already an ordinary def; drop the declare)")
                      end) groups;
                  if is_truly_mutual && not (List.for_all structural_for groups) then
                    raise (Reporting_basic.err_general true (locn_of_clause_group (List.concat groups))
                      "Lean backend: 'declare {lean} structural val' in a mutual block requires EVERY member to carry it (all-or-none: Lean's mutual structural recursion needs a termination_by clause on each member)")
                end;
                (* the designated parameter of each structural member: one
                   analysis for a truly mutual block (cross-calls count),
                   one per member otherwise (a de-mutualized sibling is an
                   ordinary, already-emitted callee) *)
                let structural_assign =
                  if not any_structural then [] else begin
                    let member_of g = match g with
                      | [({term = n}, c, pats, _, _, e)] ->
                        (c, Name.to_string (Name.strip_lskip (B.const_ref_to_name n true c)),
                         pats, e, locn_of_clause_group g)
                      | _ ->
                        raise (Reporting_basic.err_general true (locn_of_clause_group g)
                          "Lean backend: internal error — structural member is not a single clause") in
                    let run members =
                      try lean_structural_assign members
                      with Structural_refused (l, msg) ->
                        raise (Reporting_basic.err_general true l
                          (String.concat "" ["Lean backend: 'declare {lean} structural val' refused — "; msg])) in
                    if is_truly_mutual then run (List.map member_of groups)
                    else List.concat_map (fun g ->
                        if structural_for g then run [member_of g] else []) groups
                  end in
                let structural_clause g =
                  match group_cref g with
                  | Some c when any_structural && structural_for g ->
                    let i = List.assoc c structural_assign in
                    let pats = match g with [(_, _, pats, _, _, _)] -> pats | _ -> [] in
                    let pname = match lean_strip_pat (List.nth pats i) with
                      | P_var n | P_var_annot (n, _) ->
                        lean_escape_keyword (Name.to_string (Name.strip_lskip n))
                      | _ ->
                        raise (Reporting_basic.err_general true (locn_of_clause_group g)
                          "Lean backend: internal error — designated structural parameter is not a variable") in
                    Output.flat [from_string "\ntermination_by structural "; from_string pname; from_string "\n"]
                  | _ -> emp in
                (* A POLYMORPHIC definition with no
                   explicit parameters (`def fail {a} [Inhabited a] : a :=
                   failwithI "fail"`, LemLib's Assert_extra.fail) compiles to a
                   function of erased/instance arguments, so every USE
                   `@fail Char inst` is a closed term. Lean's closed-term
                   extraction hoists it into a module-initialisation constant:
                   evaluated when the module LOADS, not when the branch is
                   reached (linksem's hex_char_of_nibble `else fail` made every
                   program importing missing_pervasives panic at start-up; the
                   message is suppressed during initialisation, so under
                   LEAN_ABORT_ON_PANIC=1 it was a silent SIGABRT). OCaml
                   inlines `fail` as `assert false` at the use. `never_extract`
                   keeps each use where it is, as `failwithI` itself has. *)
                let never_extract_for g =
                  if inside_instance then emp
                  else match g with
                    | ((_, c, _, _, _, _) :: _) when
                        (let cty = (c_env_lookup Ast.Unknown A.env.c_env c).const_type in
                         List.for_all (fun (_, _, pats, _, _, _) -> pats = []) g &&
                         not (Types.TNset.is_empty (Types.free_vars cty)) &&
                         (* a point-free function (`elem = listMemberBy ...`)
                            only builds a closure: nothing to protect *)
                         (match (Types.head_norm A.env.t_env cty).Types.t with
                          | Types.Tfn _ -> false | _ -> true)) ->
                      from_string "@[never_extract] "
                    | _ -> emp
                in
                let rec def_keyword_for g = Output.flat [never_extract_for g; def_keyword_base g]
                and def_keyword_base g =
                  if inside_instance then emp
                  else if any_structural && structural_for g then
                    from_string "def"
                  else if demutualized <> None then
                    (* de-mutualized member: keyword by ITS OWN recursion
                       and ITS OWN termination declare *)
                    (if group_self_recursive g && not (auto_term_for g) then
                       from_string "partial def"
                     else from_string "def")
                  else if is_recursive && not try_term then
                    from_string "partial def"
                  else
                    from_string "def"
                in
                (* Reader lifting: the lifted set is computed by the module
                   pre-pass (see lean_reader_prepass); emission just consults
                   membership. Instance fields cannot take extra parameters:
                   fail closed if an instance method needs the reader. *)
                let register_group group =
                  let lifted = List.exists (fun (_, c, _, _, _, _) ->
                      Types.Cdset.mem c !St.reader_lifted) group in
                  let needs = List.exists (fun (_, _, _, _, _, e) ->
                      exp_needs_reader e) group in
                  if needs && inside_instance then
                    raise (Reporting_basic.err_general true (locn_of_clause_group group)
                      "Lean backend: reader-lifted call inside an instance method (unsupported: instance fields cannot take extra parameters)");
                  lifted && not inside_instance
                in
                let render_group group =
                  match group with
                  | [] -> emp
                  | [single_clause] ->
                    (* Single clause: render as before *)
                    funcl inside_instance i_ref_opt constraints tv_set single_clause
                  | first_clause :: rest_clauses ->
                    (* Multi-clause: use Lean 4 equation compiler syntax *)
                    let ({term = n}, c, pats, typ_opt, _skips, _e) = first_clause in
                    let n = B.const_ref_to_name n true c in
                    let name_skips = Name.get_lskip n in
                    let name = from_string (Name.to_string (Name.strip_lskip n)) in
                    (* Get the full type from the const_descr *)
                    let cd = c_env_lookup Ast.Unknown A.env.c_env c in
                    let full_type = pat_typ (C.t_to_src_t cd.const_type) in
                    let tv_set_out =
                      if inside_instance then emp
                      else
                        let tv = Types.free_vars cd.const_type in
                        if Types.TNset.cardinal tv = 0 then emp
                        else Output.flat [from_string " "; let_type_variables true tv]
                    in
                    let constraints_sep =
                      if constraints = emp then emp else from_string " "
                    in
                    (* Render each clause as | pat1, pat2, ... => body *)
                    let render_equation ({term = _}, _, pats, _, skips, e) =
                      let pat_out = concat_str ", " (List.map def_pattern pats) in
                      let body =
                        if needs_parens (C.exp_to_term e) then
                          Output.flat [from_string "("; exp inside_instance e; from_string ")"]
                        else exp inside_instance e
                      in
                      flatten_newlines (Output.flat [
                        from_string "\n  | "; pat_out; from_string " =>"; ws skips; from_string " "; body
                      ])
                    in
                    let equations = Output.flat (List.map render_equation (first_clause :: rest_clauses)) in
                    Output.flat [
                      ws name_skips; from_string " "; name; tv_set_out; constraints_sep; constraints;
                      fuel_binder_output (); ireader_binder_output (); inhabited_binder_output (); reader_binder_output ();
                      from_string " : "; full_type; equations
                    ]
                in
                (* Block-level fuel plan: every fuel'd def of
                   this block, so cross-member calls inside a fuel'd mutual
                   block rewrite to '(worker lemFuel)' — each hop passes the
                   decremented binder and Lean sees mutual structural
                   recursion on fuel. All-or-none per mutual block: a
                   non-fuel'd member calling a fuel'd sibling would use the
                   wrapper and reset the fuel, defeating termination. *)
                let fuel_plan =
                  List.filter_map (function
                    | [({term = n}, c, _, _, _, _)] when fuel_sentinel_for c <> None ->
                        let base = Name.to_string (Name.strip_lskip (B.const_ref_to_name n true c)) in
                        Some (c, String.concat "" [base; "_lemFuel"])
                    | ((({term = _}, c, _, _, _, _) :: _ :: _) as g) when fuel_sentinel_for c <> None ->
                        raise (Reporting_basic.err_general true (locn_of_clause_group g)
                          "Lean backend: 'declare {lean} fuel val' on a multi-clause definition (unsupported)")
                    | _ -> None) groups in
                if is_truly_mutual && fuel_plan <> []
                   && List.length fuel_plan <> List.length groups then
                  raise (Reporting_basic.err_general true (locn_of_clause_group (List.concat groups))
                    "Lean backend: fuel in a mutual block requires EVERY member to carry a 'declare {lean} fuel val' (all-or-none)");
                (* Does any body of this block reach the ambient fuel OUTSIDE
                   the block (a fuel'd callee, a fuel_consumer, a fuel-lifted
                   def)? Then the block's workers take the `[LemFuel]` binder
                   (they pass the ambient on — every fuel'd callee starts its
                   counter from the FULL ambient, never from the caller's
                   remaining counter); a leaf worker takes none (its wrapper
                   alone applies the ambient) — the reader-binder discipline
                   applied to fuel. Self/sibling calls pass the counter and
                   are excluded from the test. *)
                let block_crefs =
                  List.filter_map (fun g -> match g with
                    | (_, c, _, _, _, _) :: _ -> Some c | [] -> None) groups in
                let workers_need_fuel =
                  (not !St.rendering_comment)
                  && List.exists (fun g ->
                       List.exists (fun (_, _, _, _, _, e) ->
                           let ue = add_exp_entities empty_used_entities e in
                           List.exists (fun cref ->
                               not (List.mem cref block_crefs)
                               && (is_ambient_fuelled_cref cref || is_fuel_consumer_cref cref
                                   || Types.Cdset.mem cref !St.fuel_lifted))
                             ue.used_consts) g) groups in
                (* declare {lean} fuel_measure val in a truly mutual fuel'd
                   block: all-or-none, as for the fuel itself (each member's
                   wrapper starts the SHARED counter from its own measure;
                   a member left on the ambient would make the block's
                   callers fuel-lifted while its siblings are fuel-free) *)
                if is_truly_mutual && fuel_plan <> []
                   && List.exists (fun (c, _) -> fuel_measure_for c <> None) fuel_plan
                   && not (List.for_all (fun (c, _) -> fuel_measure_for c <> None) fuel_plan) then
                  raise (Reporting_basic.err_general true (locn_of_clause_group (List.concat groups))
                    "Lean backend: 'declare {lean} fuel_measure val' in a mutual block requires EVERY member to carry it (FM-mutual, all-or-none: the members share one counter)");
                let saved_plan = !St.fuel_workers in
                St.fuel_workers := fuel_plan;
                Fun.protect ~finally:(fun () -> St.fuel_workers := saved_plan) @@ fun () ->
                (* fuel_measure obligations are consed per member while the
                   block's bodies render (member order) and defs folds the
                   blocks last-to-first: reverse this block's segment
                   afterwards so the auxiliary file lists them in
                   declaration order *)
                let obligations_before = !St.measure_obligations in
                let bodies_raw = List.map (fun g ->
                    (* Fuel emission (declare {lean} fuel val): single-clause,
                       non-instance. Composes with truly-mutual blocks and
                       with reader lifting — INCLUDING inside a mutual block
                       (the prepass lifts a mutual Val_def's members all-or-none,
                       and the per-member emission below is generic in
                       `lifted`). Fail closed on the remaining unsupported
                       combinations: supply x truly-mutual, reader_seed x
                       mutual, anything inside an instance. *)
                    let fuel_info = match g with
                      | [({term = n}, c, _, _, _, _)] ->
                          (match fuel_sentinel_for c with
                           | Some s -> Some (n, c, s)
                           | None -> None)
                      | (({term = _}, c, _, _, _, _) :: _) ->
                          (match fuel_sentinel_for c with
                           | Some _ ->
                             raise (Reporting_basic.err_general true (locn_of_clause_group g)
                               "Lean backend: 'declare {lean} fuel val' on a multi-clause definition (unsupported)")
                           | None -> None)
                      | [] -> None in
                    (* reader_seed defs: not lifted; with N declared readers
                       their first N arguments become the injection values
                       for the body — one per reader, positionally in the
                       GLOBAL SORTED reader order (get_reader_params: the
                       binder order every lifted def and consumer stub
                       uses, so there is ONE order everywhere). The former
                       "exactly one declared reader" guard is gone: its
                       concern — one seed name overriding EVERY reader
                       binder would silently conflate them — is met by the
                       per-reader association. Fail closed on every
                       unsupported combination: no reader at all (a seed
                       with nothing to seed), fewer parameters than
                       readers, a non-variable seed pattern. *)
                    let seed_info = match g with
                      | [(_, c, pats, _, _, _)] when is_seed_cref c ->
                          let readers = get_reader_params () in
                          let n = List.length readers in
                          let reader_name cref =
                            Name.to_string (Path.get_name
                              (c_env_lookup Ast.Unknown A.env.c_env cref).const_binding) in
                          let order () =
                            String.concat ", " (List.map (fun (cref, _) -> reader_name cref) readers) in
                          if n = 0 then
                            raise (Reporting_basic.err_general true (locn_of_clause_group g)
                              "Lean backend: reader_seed declared but no reader is declared (nothing to seed)");
                          if List.length pats < n then
                            raise (Reporting_basic.err_general true (locn_of_clause_group g)
                              (Printf.sprintf
                                "Lean backend: reader_seed def must take %d seed argument%s (one per declared reader, in the global sorted reader order: %s)"
                                n (if n = 1 then "" else "s") (order ())));
                          let seed_pats = List.filteri (fun i _ -> i < n) pats in
                          Some (List.mapi (fun i ((cref, pname), p) ->
                              match p.term with
                              | P_var v | P_var_annot (v, _) ->
                                (pname, Name.to_string (Name.strip_lskip v))
                              | _ ->
                                raise (Reporting_basic.err_general true (locn_of_clause_group g)
                                  (Printf.sprintf
                                    "Lean backend: reader_seed def's seed arguments must be simple variables (argument %d of %d, the seed for reader %s, is not)"
                                    (i + 1) n (reader_name cref))))
                            (List.combine readers seed_pats))
                      | (( _, c, _, _, _, _) :: _) when is_seed_cref c ->
                          raise (Reporting_basic.err_general true (locn_of_clause_group g)
                            "Lean backend: reader_seed on a multi-clause or mutual definition (unsupported)")
                      | _ -> None in
                    (match seed_info with
                     | Some _ when is_truly_mutual ->
                       raise (Reporting_basic.err_general true (locn_of_clause_group g)
                         "Lean backend: reader_seed in a mutual block (unsupported; the mutual partner would escape lifting)")
                     | Some _ when inside_instance ->
                       raise (Reporting_basic.err_general true (locn_of_clause_group g)
                         "Lean backend: reader_seed inside an instance (unsupported)")
                     | Some _ when fuel_info <> None ->
                       raise (Reporting_basic.err_general true (locn_of_clause_group g)
                         "Lean backend: reader_seed combined with fuel (unsupported)")
                     | _ -> ());
                    (* The reserved-name contract (the table at
                       lean_reserved_exact_names; the design note
                       doc/notes/2026-08-22_arc14-reserved-names.md): the
                       backend synthesizes binders such as `lemFuel` (fuel)
                       and `_lemReader_<name>` (reader injection) into user
                       signatures. A user binder with one of those names
                       silently SHADOWS the synthesized binder — a worker
                       that matched the user's `lemFuel` returned the
                       sentinel for every call — so it is refused at
                       generation time. Checked: the clause PARAMETERS and
                       every binder inside the compiled clause BODY
                       (exp_bound_names: a match/let/fun/do binder shadows
                       the synthesized binder at the self-call and injection
                       sites just as a parameter does; a tuple-pattern
                       binder in a reader body once compiled and ran wrong
                       — negative probes neg_fuel_shadow_body,
                       neg_reader_shadow_body). *)
                    let reserved_binder_check () =
                      let bound = List.concat_map (fun (_, _, pats, _, _, e) ->
                          List.concat_map (fun p ->
                            List.map (fun a ->
                              Name.to_string (Name.strip_lskip a.term))
                              (Pattern_syntax.pat_vars_src p)) pats
                          @ exp_bound_names e) g in
                      List.iter (fun n ->
                        if lean_is_reserved_binder n then
                          raise (Reporting_basic.err_general true (locn_of_clause_group g)
                            (Printf.sprintf
                              "Lean backend: binder '%s' collides with a reserved synthesized binder (the reserved-name contract: %s are the backend's, in parameters AND clause bodies; a shadowed fuel/reader/supply/hypothesis binder is silently wrong) — rename the variable" n (lean_reserved_names_text lean_reserved_binder_names))))
                        bound;
                      (* and what the body's constants RENDER as (mechanism
                         comment at lean_reserved_capture_check) *)
                      List.iter (fun ({term = n}, _, _, _, _, e) ->
                          lean_reserved_capture_check A.env (locn_of_clause_group g)
                            (Name.to_string (Name.strip_lskip n)) e) g in
                    (* --- Supply lifting: group classification + the
                       fail-closed guards (G-inst; the v1 restrictions
                       on truly-mutual blocks and multi-clause groups —
                       named errors, the fuel machinery's precedent;
                       everything else the supply net + transform guard).
                       All inert while rendering block comments (dead
                       text). --- *)
                    let supply_lifted_g =
                      (not !St.rendering_comment)
                      && List.exists (fun (_, c, _, _, _, _) ->
                             Types.Cdset.mem c !St.supply_lifted) g in
                    let supply_needs_g =
                      (not !St.rendering_comment)
                      && List.exists (fun (_, _, _, _, _, e) -> exp_needs_supply e) g in
                    if supply_needs_g && inside_instance then
                      (* G-inst *)
                      raise (Reporting_basic.err_general true (locn_of_clause_group g)
                        "Lean backend: supply draw (or supply-lifted call) inside an instance method (unsupported: instance fields cannot take extra parameters or change their result type)");
                    if supply_lifted_g && is_truly_mutual then
                      raise (Reporting_basic.err_general true (locn_of_clause_group g)
                        "Lean backend: supply lifting in a (truly) mutual block (unsupported; extend when needed — acyclic rec-and blocks de-mutualize and thread fine)");
                    if supply_lifted_g && List.length g > 1 then
                      raise (Reporting_basic.err_general true (locn_of_clause_group g)
                        "Lean backend: supply lifting on a multi-clause definition (unsupported; write the clauses as a single match)");
                    (if fuel_info <> None || seed_info <> None then reserved_binder_check ()
                     else if List.exists (fun (_, cr, _, _, _, _) ->
                              Types.Cdset.mem cr !St.reader_lifted
                              || Types.Cdset.mem cr !St.supply_lifted) g then reserved_binder_check ());
                    let lifted = register_group g in
                    (* Fuel lifting: membership computed by lean_fuel_prepass
                       (a fuel'd def is always a member: its wrapper takes the
                       ambient). Inert for block comments. *)
                    let fuel_lifted_g =
                      (not !St.rendering_comment)
                      && List.exists (fun (_, c, _, _, _, _) ->
                             Types.Cdset.mem c !St.fuel_lifted) g in
                    if (not !St.rendering_comment) && inside_instance
                       && List.exists (fun (_, _, _, _, _, e) -> exp_needs_fuel e) g then
                      raise (Reporting_basic.err_general true (locn_of_clause_group g)
                        "Lean backend: fuel'd (or fuel-lifted) call inside an instance method (unsupported: instance fields cannot take the [LemFuel] binder)");
                    (match seed_info with
                     | Some _ when lifted ->
                       raise (Reporting_basic.err_general true (locn_of_clause_group g)
                         "Lean backend: reader_seed def unexpectedly reader-lifted")
                     | _ -> ());
                    let saved_seed = !St.reader_seed_param in
                    St.reader_seed_param := seed_info;
                    Fun.protect ~finally:(fun () -> St.reader_seed_param := saved_seed) @@ fun () ->
                    (match fuel_info with
                     | Some _ when inside_instance ->
                       raise (Reporting_basic.err_general true (locn_of_clause_group g)
                         "Lean backend: 'declare {lean} fuel val' inside an instance (unsupported)")
                     | _ -> ());
                    (* fuel x reader composes: the worker's fuel
                       counter is emitted BEFORE the reader binders, so the
                       point-free wrapper 'worker LemFuel.fuel' has the
                       reader-prefixed type and lifted callers inject into
                       the wrapper as for any lifted def. In a truly-mutual
                       block the same holds per member: every
                       member is lifted together (the prepass unions the
                       block's defined set), each worker/wrapper/obligation/
                       `_zero` lemma takes the readers through `lifted`, and
                       a sibling call `(sibling_lemFuel lemFuel <readers>)`
                       re-injects them at the St.fuel_workers rewrite. *)
                    (* [Inhabited tv] binders for this group,
                       from the threading pre-pass (instance methods are
                       never threaded — the pre-pass guard errors first). *)
                    let thread_names =
                      if inside_instance then []
                      else match group_cref g with
                        | Some c -> (match lean_thread_lookup c with
                            | Some (_, ns) -> ns
                            | None -> [])
                        | None -> [] in
                    let saved_inh = !St.inhabited_binder in
                    St.inhabited_binder := thread_names;
                    Fun.protect ~finally:(fun () -> St.inhabited_binder := saved_inh) @@ fun () ->
                    (* Instance readers: the group's lifted set, for every
                       emitted piece — body or fuel worker, wrapper, `_zero`
                       lemma, measure obligation (a fuel'd group's worker
                       binds them unconditionally: unlike the fuel, whose
                       worker recurses on its own counter, the class is read
                       by the body itself). *)
                    let saved_irb = !St.ireader_binder in
                    St.ireader_binder :=
                      (if inside_instance || !St.rendering_comment then []
                       else ireader_group_binders
                           (List.map (fun (_, c, _, _, _, _) -> c) g));
                    Fun.protect ~finally:(fun () -> St.ireader_binder := saved_irb) @@ fun () ->
                    match fuel_info with
                    | None ->
                      let saved = !St.reader_binder in
                      let saved_sb = !St.supply_binder in
                      let saved_fb = !St.fuel_binder in
                      St.reader_binder := lifted;
                      St.supply_binder := supply_lifted_g && not inside_instance;
                      St.fuel_binder := fuel_lifted_g && not inside_instance;
                      Fun.protect ~finally:(fun () ->
                          St.reader_binder := saved;
                          St.supply_binder := saved_sb;
                          St.fuel_binder := saved_fb)
                        (fun () ->
                           (def_keyword_for g,
                            Output.flat [render_group g; structural_clause g], emp))
                    | Some (n, c, s) ->
                      let base_name = Name.to_string (Name.strip_lskip (B.const_ref_to_name n true c)) in
                      let worker = String.concat "" [base_name; "_lemFuel"] in
                      let cd = c_env_lookup Ast.Unknown A.env.c_env c in
                      let tv = Types.free_vars cd.const_type in
                      let tv_out =
                        if Types.TNset.cardinal tv = 0 then emp
                        else Output.flat [from_string " "; let_type_variables true tv] in
                      let saved_e = !St.fuel_emit in
                      let saved_rb = !St.reader_binder in
                      let saved_sb = !St.supply_binder in
                      let saved_fb = !St.fuel_binder in
                      St.fuel_emit := Some s;
                      St.reader_binder := lifted;
                      St.supply_binder := supply_lifted_g && not inside_instance;
                      (* the hoisted `function`-tail binders the sentinel is
                         applied to (mechanism comment at lean_hoist_tail_binders) *)
                      let saved_ta = !St.tail_sentinel_args in
                      St.tail_sentinel_args :=
                        (match List.assoc_opt c !St.tail_hoisted with Some ns -> ns | None -> []);
                      (* the wrapper ALWAYS takes the ambient (it starts the
                         counter from it — emitted literally below); the
                         worker only when it passes it on (workers_need_fuel) *)
                      St.fuel_binder := workers_need_fuel && not inside_instance;
                      (* worker name must agree with the block-level plan —
                         a real error, not a bare assert (`assert` is
                         compiled out under -noassert). *)
                      if List.assoc_opt c !St.fuel_workers <> Some worker then
                        raise (Reporting_basic.err_general true Ast.Unknown
                          "Lean backend: internal error — fuel worker name disagrees with the block-level fuel plan");
                      Fun.protect ~finally:(fun () ->
                          St.fuel_emit := saved_e;
                          St.reader_binder := saved_rb;
                          St.supply_binder := saved_sb;
                          St.fuel_binder := saved_fb;
                          St.tail_sentinel_args := saved_ta)
                        (fun () ->
                          let body = render_group g in
                          (* A parameter pattern's binder: a variable (bare,
                             annotated `(x : t)`, or parenthesised), or a
                             wildcard (fresh name); anything else has no
                             name — the `_zero` lemma is then not
                             generated, a measured wrapper is refused.
                             Returns (binder, argument, lem name option). *)
                          let pats = match g with
                            | (_, _, pats, _, _, _) :: _ -> pats
                            | [] -> [] in
                          let rec binder_of i (p : pat) =
                            let mk nm t lemname =
                              Some (Output.flat [from_string " ("; nm; from_string " : "; t; from_string ")"],
                                    Output.flat [from_string " "; nm], lemname, p.typ) in
                            let lem_of v = Name.to_string (Name.strip_lskip v) in
                            match p.term with
                            | P_var v -> mk (name_var_output v) (pat_typ (C.t_to_src_t p.typ)) (Some (lem_of v))
                            | P_var_annot (v, t) -> mk (name_var_output v) (pat_typ t) (Some (lem_of v))
                            | P_wild _ ->
                              mk (from_string (Printf.sprintf "_x%d" (i + 1))) (pat_typ (C.t_to_src_t p.typ)) None
                            | P_typ (_, p', _, _, _) | P_paren (_, p', _) -> binder_of i p'
                            | _ -> None in
                          let binders_and_args = List.mapi binder_of pats in
                          let all_named = not (List.exists (fun o -> o = None) binders_and_args) in
                          let bs = List.filter_map (fun o -> o) binders_and_args in
                          let npats = List.length pats in
                          (* the type after the head's parameters: a definition
                             whose head binds FEWER parameters than its type has
                             arrows (a point-free tail — cerberus `liftAction`,
                             `one_step_unseq_aux`) leaves the codomain a function
                             type *)
                          let rec codomain_after l n (t : Types.t) =
                            if n = 0 then t
                            else match t.Types.t with
                              | Types.Tfn (_, b) -> codomain_after l (n - 1) b
                              | _ ->
                                raise (Reporting_basic.err_general true l
                                  "Lean backend: internal error — a fuel'd definition has more parameters than its type has arrows") in
                          let arity =
                            let rec go (t : Types.t) = match t.Types.t with
                              | Types.Tfn (_, b) -> 1 + go b | _ -> 0 in
                            go cd.const_type in
                          (* class-constraint binders must be re-emitted on
                             the wrapper too ([Eq0 a]-style constrained defs
                             failed to elaborate without them) *)
                          let cons_out =
                            if constraints = emp then emp
                            else Output.flat [from_string " "; constraints] in
                          let wrapper_and_obligation =
                            match fuel_measure_for c with
                            | None ->
                          (* Point-free wrapper at the AMBIENT fuel
                             (`worker LemFuel.fuel`): call sites are
                             unchanged, `@f ⟨n⟩ = f_lemFuel n` unfolds
                             definitionally, and a theorem quantifies over
                             the instance. No numeral is ever emitted here
                             ([USER 2026-09-03], "No magic values"). *)
                          (* A lifted worker's wrapper has the reader-prefixed
                             type: reader binders sit between the
                             fuel counter and the original arguments, so
                             'worker LemFuel.fuel' is reader-first. *)
                          let reader_arrows =
                            if not lifted then emp else
                            Output.flat (List.map (fun (cref, _) ->
                                Output.flat [from_string "(";
                                             pat_typ (C.t_to_src_t (reader_value_typ cref));
                                             from_string ") -> "])
                              (get_reader_params ())) in
                          (* A supply-lifted worker's wrapper: the supply
                             binders sit after the readers (fixed order:
                             [LemFuel], [Inhabited], fuel counter, readers,
                             supply, original arguments), and the result is
                             the value×supply pair — 'worker LemFuel.fuel'
                             stays point-free. *)
                          let supply_arrows =
                            if not !St.supply_binder then emp else
                            Output.flat (List.map (fun _ -> from_string "Nat -> ")
                              (get_supply_params ())) in
                          let result_typ_out =
                            if !St.supply_binder then
                              supply_transformed_typ_output cd
                                (match g with
                                 | (_, _, pats, _, _, _) :: _ -> List.length pats
                                 | [] -> 0)
                            else pat_typ (C.t_to_src_t cd.const_type) in
                          Output.flat [
                            from_string "\n\n";
                            from_string "def "; from_string base_name; tv_out; cons_out;
                            from_string " [LemFuel]"; ireader_binder_output (); inhabited_binder_output ();
                            from_string " : "; reader_arrows; supply_arrows;
                            result_typ_out;
                            from_string " := "; from_string worker;
                            from_string " LemFuel.fuel"; from_string "\n"]
                            | Some (measure, hyp_opt) ->
                          (* declare {lean} fuel_measure val (mechanism
                             comment at lean_fuel_measure_for): the wrapper
                             binds the parameters and starts the worker's
                             counter from the DATA MEASURE — no ambient
                             fuel is read here; the binder `[LemFuel]`
                             appears only if the body passes the ambient
                             on to another fuel'd function (then, and only
                             then, the def is fuel-lifted — the fixpoint
                             and workers_need_fuel must agree). *)
                          let l = locn_of_clause_group g in
                          if is_library_module !St.current_module_name then
                            raise (Reporting_basic.err_general true l
                              (Printf.sprintf
                                "Lean backend: 'declare {lean} fuel_measure val %s' in a library module (FM-library: the library's auxiliary files are not built, so the sufficiency obligation would have no home)"
                                base_name));
                          if !St.supply_binder then
                            raise (Reporting_basic.err_general true l
                              (Printf.sprintf
                                "Lean backend: 'declare {lean} fuel_measure val %s' on a supply-lifted definition (FM-supply: unsupported combination; extend when needed)"
                                base_name));
                          if not all_named then
                            raise (Reporting_basic.err_general true l
                              (Printf.sprintf
                                "Lean backend: 'declare {lean} fuel_measure val %s' on a definition whose parameter is a destructuring pattern (the measured wrapper binds every parameter by name — write the destructuring as a match in the body)"
                                base_name));
                          if fuel_lifted_g <> workers_need_fuel then
                            raise (Reporting_basic.err_general true l
                              "Lean backend: internal error — the fuel fixpoint and the block's ambient-reach test disagree on a measured definition");
                          let params = List.filter_map (fun (_, _, lemname, ty) ->
                              match lemname with
                              | Some ln -> Some (ln, (lean_escape_keyword ln, ty))
                              | None -> None) bs in
                          let measure_out = lean_render_measure A.env.t_env l base_name params measure in
                          (* the `assuming` hypothesis: rendered under the
                             same scope rules;
                             it appears ONLY in the obligation, as the binder
                             `lemHyp` immediately before `lemFuel` — the
                             wrapper stays fuel-free and hypothesis-free *)
                          let hyp_out = Option.map (lean_render_hypothesis A.env.t_env l base_name params) hyp_opt in
                          let hyp_binder = match hyp_out with
                            | None -> emp
                            | Some h -> Output.flat [from_string " (lemHyp : ("; from_string h; from_string "))"] in
                          let hyp_arg = match hyp_out with
                            | None -> emp
                            | Some _ -> from_string " lemHyp" in
                          let result_out = pat_typ (C.t_to_src_t (codomain_after l npats cd.const_type)) in
                          let ambient_binder =
                            if fuel_lifted_g && not inside_instance then from_string " [LemFuel]" else emp in
                          let arg_binders = Output.flat (List.map (fun (b, _, _, _) -> b) bs) in
                          let arg_names = Output.flat (List.map (fun (_, a, _, _) -> a) bs) in
                          let reader_binders =
                            if lifted then reader_binder_output () else emp in
                          let reader_args = if lifted then reader_args_output () else emp in
                          let wrapper = Output.flat [
                            from_string "\n\n";
                            from_string "def "; from_string base_name; tv_out; cons_out;
                            ambient_binder; ireader_binder_output (); inhabited_binder_output ();
                            reader_binders; arg_binders;
                            from_string " : "; result_out;
                            from_string " := "; from_string worker;
                            from_string " ("; from_string measure_out; from_string ")";
                            reader_args; arg_names; from_string "\n"] in
                          (* The sufficiency OBLIGATION, stated here and
                             proved in `<Module>_lemMeasureProofs` (a
                             hand-written module the auxiliary file
                             imports): at every fuel at or above the
                             measure the worker equals the wrapper — the
                             wrapper's value is the fuel-independent value
                             of the recursion; `f x = f_lemFuel (measure) x`
                             itself is `rfl`. *)
                          let proofs_module =
                            String.concat "" [!St.current_module_name; "_lemMeasureProofs"] in
                          let thm = String.concat "" [base_name; "_measure_sufficient"] in
                          let obligation = Output.flat ([
                            from_string "\n/- lem: fuel_measure obligation for `"; from_string base_name;
                            from_string "` (generated; declare {lean} fuel_measure val "; from_string base_name;
                            from_string " = `"; from_string (String.trim measure);
                            (match hyp_opt with
                             | None -> from_string "`)"
                             | Some h -> Output.flat [from_string "` assuming `"; from_string (String.trim h);
                                                      from_string "`; the hypothesis is the binder `lemHyp`, before `lemFuel` — on inputs violating it the wrapper may exhaust)"]);
                            from_string ": the worker is fuel-STABLE at the measure (equal to the wrapper at every fuel at or above it). The proof is hand-written in `";
                            from_string proofs_module; from_string "." ; from_string thm;
                            from_string "`, stated with exactly these binders; a missing or mistyped theorem fails the build (a `sorry` is the sorry/axiom gates' job). -/\n";
                            from_string "theorem "; from_string thm; tv_out; cons_out;
                            ambient_binder; ireader_binder_output (); inhabited_binder_output ();
                            reader_binders; arg_binders; hyp_binder;
                            from_string " (lemFuel : Nat) (lemMeasureLe : ("; from_string measure_out;
                            from_string ") ≤ lemFuel) :\n    "; from_string worker; from_string " lemFuel";
                            reader_args; arg_names; from_string " = "; from_string base_name;
                            reader_args; arg_names; from_string " :=\n  ";
                            from_string proofs_module; from_string "."; from_string thm;
                            reader_args; arg_names; hyp_arg; from_string " lemFuel lemMeasureLe\n"]) in
                          St.measure_obligations := obligation :: !St.measure_obligations;
                          wrapper in
                          let wrapper = wrapper_and_obligation in
                          (* The exhaustion lemma `<worker>_zero`: the
                             worker at counter 0 IS the sentinel, by rfl —
                             kernel-transparent, so "exhausted" is
                             recognisable wherever it arises (consumer
                             requirement, refined-cerberus request §3).
                             Generated when every parameter is a plain
                             variable or a wildcard (the statement needs
                             names for the arguments); a destructuring
                             parameter pattern gets an explanatory comment
                             instead — state that lemma by hand. *)
                          let zero_lemma =
                            if not all_named then
                              Output.flat [
                                from_string "/- lem: "; from_string worker;
                                from_string "_zero not generated: a parameter is a destructuring pattern; state the exhaustion lemma by hand -/\n"]
                            else begin
                              let supply_names =
                                if not !St.supply_binder then emp else
                                Output.flat (List.map (fun (_, pname) ->
                                    Output.flat [from_string " "; from_string pname])
                                  (get_supply_params ())) in
                              (* a point-free tail (npats < arity): ascribe the
                                 codomain to the LHS, or the RHS lambda's implicit
                                 type arguments have nothing to unify with
                                 (Cerberus's liftAction_lemFuel_zero:
                                 `don't know how to synthesize implicit argument`);
                                 not under supply lifting, whose codomain is the
                                 transformed pair type (no such case exists) *)
                              let tail_ascription =
                                if npats < arity && not !St.supply_binder then
                                  Some (pat_typ (C.t_to_src_t (codomain_after (locn_of_clause_group g) npats cd.const_type)))
                                else None in
                              Output.flat ([
                                from_string "theorem "; from_string worker; from_string "_zero";
                                tv_out; cons_out;
                                fuel_binder_output (); ireader_binder_output (); inhabited_binder_output ();
                                reader_binder_output (); supply_binder_output ()]
                                @ List.map (fun (b, _, _, _) -> b) bs
                                @ [from_string " :\n    ";
                                   (if tail_ascription <> None then from_string "(" else emp);
                                   from_string worker; from_string " 0";
                                   (if lifted then reader_args_output () else emp);
                                   supply_names]
                                @ List.map (fun (_, a, _, _) -> a) bs
                                @ (match tail_ascription with
                                   | Some t -> [from_string " : "; t; from_string ")"]
                                   | None -> [])
                                @ [from_string " = "; fuel_sentinel_output s; from_string " := rfl\n"])
                            end in
                          (* Wrapper (and its lemma) are returned separately:
                             in a mutual block they must be emitted AFTER
                             'end', or the wrapper would join the recursion
                             set. *)
                          (from_string "def", body, Output.flat [wrapper; zero_lemma]))
                  ) groups in
                let bodies =
                  let n_new = List.length !St.measure_obligations - List.length obligations_before in
                  let added = List.filteri (fun i _ -> i < n_new) !St.measure_obligations in
                  St.measure_obligations := List.rev added @ obligations_before;
                  bodies_raw in
                let rec_skips =
                  if is_recursive && not inside_instance then
                    ws skips'
                  else emp
                in
                if is_truly_mutual then
                  Output.flat [
                    ws skips; from_string "mutual\n"; rec_skips;
                    concat_str "\n" (List.map (fun (k, b, _) -> Output.flat [k; b]) bodies);
                    from_string "\nend";
                    (* fuel wrappers of a mutual block, after 'end' *)
                    Output.flat (List.map (fun (_, _, w) -> w) bodies)
                  ]
                else
                  (* de-mutualized members need explicit separation: an
                     and-member's leading skips carry no newline *)
                  let sep = if demutualized <> None then from_string "\n" else emp in
                  Output.flat [
                    ws skips; rec_skips;
                    Output.flat (List.map (fun (k, b, w) ->
                        Output.flat [sep; k; b; w]) bodies)
                  ]
              else
                from_string "\n/- lem: removed a recursive definition for another backend -/"
          | Let_inline (skips, _, _, _, _, _, _, _) ->
              (* Let_inline declarations are inlined at use sites during compilation.
                 The backend emits nothing — the definition body appears inline. *)
              ws skips
      end
    (* Inductive relation (indreln) rendering. Phases:
       1. Gather unique relation names with their const_descr_refs
       2. Set St.indreln_params so exp can insert type parameters for
          polymorphic self-references in premises
       3. Build inductive definitions using renamed names from const_descr
          (handles cross-module collisions like thread_trans → thread_trans0)
       4. Render clauses with St.prop_equality set so antecedents use
          propositional = instead of BEq ==
       St.indreln_params is saved/restored so nested indreln blocks don't
       clobber the outer scope. *)
    and clauses (inside_instance: bool) clause_list =
      (* Gather unique relation names from clauses, paired with their
         const_descr_ref so we can look up the renamed name for output *)
      let gather_names clause_list =
        let rec gather_names_aux buffer clauses =
          match clauses with
            | []    -> buffer
            | (Rule(_,_, _, _, _, _, _, name_lskips_annot, c, _),_)::xs ->
              let name = name_lskips_annot.term in
              let name = Name.strip_lskip name in
              (* Name.compare, not polymorphic Stdlib.compare on the
                 abstract Name.t. *)
              if List.exists (fun (n, _) -> Name.compare n name = 0) buffer then
                gather_names_aux buffer xs
              else
                gather_names_aux ((name, c)::buffer) xs
        in
          gather_names_aux [] clause_list
      in
      let gathered = gather_names clause_list in
      (* A relation in the fuel-lifted set (its
         premises reach the ambient fuel; lean_fuel_prepass lifts the whole
         block) takes `[LemFuel]` as an inductive parameter, and its
         premises render inside a fuel scope. Inert for block comments. *)
      let fuel_lifted_rel =
        (not !St.rendering_comment)
        && List.exists (fun (_, c) -> Types.Cdset.mem c !St.fuel_lifted) gathered in
      let saved_fuel_binder = !St.fuel_binder in
      if fuel_lifted_rel then St.fuel_binder := true;
      Fun.protect ~finally:(fun () -> St.fuel_binder := saved_fuel_binder) (fun () ->
      (* For polymorphic indreln: compute type parameter names per relation
         and set St.indreln_params so exp can insert them in premises. *)
      let saved_indreln_params = !St.indreln_params in
      St.indreln_params := List.filter_map (fun (_name, c_ref) ->
        let cd = c_env_lookup Ast.Unknown A.env.c_env c_ref in
        let tvs = Types.free_vars cd.const_type in
        if Types.TNset.cardinal tvs = 0 then None
        else
          let params_str = String.concat " " @@
            List.map (fun v -> Name.to_string (Types.tnvar_to_name v))
              (Types.TNset.elements tvs) in
          Some (c_ref, params_str)
      ) gathered;
      Fun.protect ~finally:(fun () -> St.indreln_params := saved_indreln_params) (fun () ->
      let compare_clauses_by_name name (Rule(_,_, _, _, _, _, _, name', _, _),_) =
        let name' = name'.term in
        let name' = Name.strip_lskip name' in
          Name.compare name name' = 0  (* not polymorphic compare *)
      in
      let indrelns =
        List.map (fun (name, c_ref) ->
          (* Use the renamed name from the constant descriptor, not the raw AST name.
             This handles cross-module collisions (e.g., indreln "thread_trans"
             renamed to "thread_trans0" to avoid conflict with imported type). *)
          let c_descr = c_env_lookup Ast.Unknown A.env.c_env c_ref in
          let (_, renamed_name, _) = Typed_ast_syntax.constant_descr_to_name (Target.Target_no_ident Target.Target_lean) c_descr in
          let name_string = Name.to_string renamed_name in
          let matching_clauses = List.filter (compare_clauses_by_name name) clause_list in
          let index_type_parts =
            match matching_clauses with
              | [] -> [from_string "Prop"]
              | (Rule(_,_, _, _, _, _, _, _, _, exp_list),_)::_ ->
                  List.map (fun t ->
                    Output.flat [
                      from_string "("; indreln_typ @@ C.t_to_src_t (Typed_ast.exp_to_typ t); from_string ")"
                    ]
                  ) exp_list
          in
          let clause_outputs =
            List.map (fun (Rule(name_lskips_t, skips0, skips, name_lskips_annot_list, skips', exp_opt, skips'', name_lskips_annot, c, exp_list),_) ->
              let constructor_name = from_string (Name.to_string (Name.strip_lskip name_lskips_t)) in
              let antecedent =
                match exp_opt with
                  | None -> emp
                  | Some e ->
                    match dest_and_exps A.env e with
                    | [] -> emp
                    | ants ->
                      (* Use propositional = in indreln antecedents instead of BEq ==.
                         Functions and other types without BEq need propositional equality. *)
                      let saved = !St.prop_equality in
                      St.prop_equality := true;
                      Fun.protect ~finally:(fun () -> St.prop_equality := saved) (fun () ->
                        flat [
                          concat_str " → "
                            (List.map (fun e ->
                                 flat [ from_string "(";
                                        exp inside_instance e;
                                        from_string ")" ]) ants);
                          from_string " → "
                        ]
                      )
              in
              let bound_variables =
                concat_str " " @@ List.map (fun b ->
                  match b with
                    | QName n -> from_string (lean_escape_keyword (Name.to_string (Name.strip_lskip n.term)))
                    | _ -> raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected binding form in indreln quantifier")
                ) name_lskips_annot_list
              in
              let binder, binder_sep =
                match name_lskips_annot_list with
                  | [] -> emp, emp
                  | _ -> from_string "∀ ", from_string ", "
              in
              let indices = concat_str " " @@ List.map (exp inside_instance) exp_list in
              let index_free_vars_set =
                List.fold_right Types.TNset.union
                  (List.map (fun t -> Types.free_vars (Typed_ast.exp_to_typ t)) exp_list)
                  Types.TNset.empty
              in
              let index_free_vars_typeset = concat_str " " @@ List.map (fun v -> from_string (Name.to_string (Types.tnvar_to_name v))) (Types.TNset.elements index_free_vars_set) in
              let relation_name = from_string name_string in
                Output.flat [
                  from_string "  | "; constructor_name; from_string " : ";
                  binder; bound_variables; binder_sep; antecedent;
                  relation_name; from_string " "; index_free_vars_typeset; from_string " "; indices
                ], index_free_vars_set
            ) matching_clauses
          in
          let all_free_vars =
            Types.TNset.elements @@
            List.fold_right Types.TNset.union (List.map snd clause_outputs) Types.TNset.empty
          in
          let free_vars_typeset =
            concat_str " " @@ List.map (fun v ->
              Output.flat [
                from_string "("; from_string (Name.to_string (Types.tnvar_to_name v)); from_string " : Type)"
              ]) all_free_vars
          in
          let index_type_sig =
            Output.flat [
              concat_str " → " index_type_parts; from_string " → Prop"
            ]
          in
          let clause_body = concat_str "\n" @@ List.map fst clause_outputs in
          let fuel_param = if fuel_lifted_rel then from_string " [LemFuel]" else emp in
          Output.flat [
            from_string name_string; from_string " "; free_vars_typeset; fuel_param; from_string " : "; index_type_sig; from_string " where\n";
            clause_body
          ]
        ) gathered
      in
        let is_mutual = List.length indrelns > 1 in
        let prefix = if is_mutual then from_string "\nmutual" else emp in
        let suffix = if is_mutual then from_string "\nend" else emp in
        Output.flat [
          prefix;
          from_string "\ninductive "; concat_str "\ninductive " indrelns;
          suffix
        ]
      ))
    and let_body inside_instance i_ref_opt top_level tv_set ((lb, _):letbind) =
      match lb with
        | Let_val (p, topt, skips, e) ->
            (* In Lean 4, `let (x : T) := val; body` is parsed as a pattern-matching
               let where x is NOT bound into body's scope. The correct syntax is
               `let x : T := val; body`. So when the pattern is P_typ at the top level,
               extract the inner pattern and emit the type annotation separately. *)
            let p_out, typ_from_pat = match p.term with
              | P_typ (_skips, inner_p, _skips', t, _skips'') ->
                  def_pattern inner_p, Some t
              | _ ->
                  def_pattern p, None
            in
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
            (* A LOCAL `let f = fun (a, b) -> ...`
               with no annotation. Lem's pattern compiler turns the tuple
               parameter into `fun p => match p with | (a, b) => ...`; with no
               expected type Lean infers a DEPENDENT motive for that match,
               and `f` gets a type like `?m img p` that cannot be applied
               further (linksem link.lem `apply_reloc`: "Function expected").
               The binding is annotated with the right-hand side's Lem type,
               which fixes the motive. A type variable the annotation needs
               but Lean does not have in scope is a loud error, never a
               silent one. *)
            let rec is_lambda (x : exp) = match C.exp_to_term x with
              | Fun _ -> true
              | Paren (_, x', _) | Typed (_, x', _, _, _) -> is_lambda x'
              | _ -> false in
            let annotate_lambda =
              not top_level && topt = None && typ_from_pat = None &&
              (match p.term with P_var _ -> true | _ -> false) && is_lambda e in
            let topt =
              match topt with
                | None when annotate_lambda ->
                    Output.flat [from_string " : "; pat_typ (C.t_to_src_t (Typed_ast.exp_to_typ e))]
                | None ->
                    (match typ_from_pat with
                      | None -> emp
                      | Some t ->
                          Output.flat [from_string " :"; pat_typ t])
                | Some (s, t) ->
                    Output.flat [
                      ws s; from_string " :"; pat_typ t
                    ]
            in
            let e = exp inside_instance e in
              Output.flat [
                p_out; tv_set_sep; tv_set; topt; ws skips; from_string " :="; e
              ]
        | Let_fun _ ->
            (* Pattern compilation transforms Let_fun into funcl before the backend *)
            raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected Let_fun in let_body (should be compiled away)")
    and funcl_aux inside_instance i_ref_opt constraints tv_set (n, pats, typ_opt, skips, e) =
      let name_skips = Name.get_lskip n in
      lean_check_reserved_def_name (exp_to_locn e)
        (Name.to_string (Name.strip_lskip n));
      let name = from_string (Name.to_string (Name.strip_lskip n)) in
      let pat_skips =
        match pats with
          | [] -> emp
          | _  -> from_string " "
      in
      let constraints_sep =
        if constraints = emp then
          emp
        else
          from_string " "
      in
      let tv_set_sep, tv_set =
        if inside_instance then
          emp, emp
        else begin
          let tv_set =
            if Types.TNset.cardinal tv_set = 0 then
              Types.free_vars (Typed_ast.exp_to_typ e)
            else tv_set
          in
          (* Filter out phantom type variables that don't appear in any explicit
             parameter types or the return type. Lean can't infer these. *)
          let sig_tvs =
            let pat_tvs = List.fold_left (fun acc p ->
              Types.TNset.union acc (Types.free_vars p.typ)
            ) Types.TNset.empty pats in
            let ret_tvs = match typ_opt with
              | None -> Types.free_vars (Typed_ast.exp_to_typ e)
              | Some (_, t) -> Types.free_vars t.typ
            in
            Types.TNset.union pat_tvs ret_tvs
          in
          let tv_set = Types.TNset.inter tv_set sig_tvs in
          if Types.TNset.cardinal tv_set = 0 then
            emp, let_type_variables true tv_set
          else
            from_string " ", let_type_variables true tv_set
        end
      in
      let typ_opt =
        match typ_opt with
          | None -> emp
          | Some (s, t) ->
              (* a supply-lifted def's result type becomes the
                 value×supply pair (linear threading — the one place
                 supply lifting departs from the reader shape) *)
              if !St.supply_binder then
                Output.flat [
                  ws s; from_string " : (("; pat_typ t; from_string ")";
                  supply_pair_suffix (); from_string ")"
                ]
              else
                Output.flat [
                  ws s; from_string " : "; pat_typ t
                ]
      in
        let body =
          if !St.supply_binder then supply_block inside_instance e
          else exp inside_instance e in
        (* Inside instance definitions, flatten newlines in the body
           expression. Without this, a multi-line body can have arguments on
           a new line at field-name indentation, which Lean misparses as a
           new field definition. *)
        let body = if inside_instance then flatten_newlines body else body in
        (match !St.fuel_emit with
         | Some sentinel ->
           let sentinel_out = fuel_sentinel_output sentinel in
           Output.flat [
             ws name_skips; from_string " "; name; from_string "_lemFuel";
             tv_set_sep; tv_set; constraints_sep; constraints;
             fuel_binder_output (); ireader_binder_output (); inhabited_binder_output ();
             from_string " (lemFuel : Nat)"; reader_binder_output (); supply_binder_output (); pat_skips;
             fun_pattern_list inside_instance pats; ws skips; typ_opt;
             from_string " := match lemFuel with\n  | 0 => ";
             sentinel_out;
             (* the succ-arm body is parenthesized like the sentinel: a
                hoisted infix head (e.g. a bind rendered prefix) followed by
                argument lines at low indentation would otherwise escape the
                match arm (Cerberus's full_eval_pexpr was the case) *)
             from_string "\n  | Nat.succ lemFuel => (";
             body;
             from_string ")"
           ]
         | None ->
           Output.flat [
             ws name_skips; from_string " "; name; tv_set_sep; tv_set; constraints_sep; constraints;
             fuel_binder_output (); ireader_binder_output (); inhabited_binder_output (); reader_binder_output (); supply_binder_output (); pat_skips;
             fun_pattern_list inside_instance pats; ws skips; typ_opt; from_string " := "; body
           ])
    and reader_binder_output () =
      if not !St.reader_binder then emp else
      Output.flat (List.map (fun (cref, pname) ->
          Output.flat [
            from_string " ("; from_string pname; from_string " : ";
            pat_typ (C.t_to_src_t (reader_value_typ cref)); from_string ")"])
        (get_reader_params ()))
    (* [Inhabited tv] instance-implicit binders for a threaded
       def (zero call-site rewrites — Lean synthesizes the instance
       arguments at every application). *)
    and inhabited_binder_output () =
      Output.flat (List.map (fun n ->
          Output.flat [from_string " [Inhabited "; from_string n; from_string "]"])
        !St.inhabited_binder)

    (* ===== The supply-threading body transform =====

       [supply_thread senv e] emits e with every draw and every lifted
       call A-normalized into let-bindings, sequenced in the EVALUATION
       ORDER OF THE OCAML TARGET — the reference semantics of the lem
       program ([USER 2026-09-03] ruling: follow the LEM semantics, i.e.
       what the OCaml backend computes). ocamlopt and
       the bytecode compiler evaluate the subexpressions of one node
       RIGHT-TO-LEFT: function-application arguments (then the head),
       tuple components, constructor arguments, list-literal elements,
       infix-operator operands, and record fields in the type's FIELD
       DECLARATION order (translcore sorts labels by position before
       the right-to-left makeblock) — while let, sequence, if and match
       are ordered as written (binding/test/scrutinee first, then the
       taken branch). Every rule below was established by a compiled
       two-target probe (tests/comprehensive/parity/probes/p_eval_order.lem,
       pin expected/p_eval_order.out) before it was implemented. It
       returns (bindings, value, senv'): the bindings to emit before the
       value, the (pure) value output, and the updated supply environment
       (supply cref -> current state variable name). Supply-free
       subexpressions delegate to the ordinary [exp] emitter verbatim.

       DETERMINISM: the transform emits only
       let-bindings, tuples, LemLib.supplySplit applications, and the
       control forms already present in the source — it contains no
       nondeterminism constructor and cannot introduce a branch point
       that was not in the input.

       Every position that cannot be threaded is a fail-closed
       generation-time error (G-λ lambdas, monadic do, comprehensions,
       bare references, arity mismatches, infix heads). *)
    and supply_fresh_name (kind : string) : string =
      let n = !St.supply_name_counter in
      St.supply_name_counter := n + 1;
      Printf.sprintf "_lemSupply%s%d" kind n
    (* Final-state tuple components, in the sorted supply-param order
       (the one canonical order, used by binders, call sites, and
       result tuples alike). *)
    and supply_state_names senv =
      List.map (fun (cref, _) ->
          match List.assoc_opt cref senv with
          | Some s -> s
          | None ->
            raise (Reporting_basic.err_general true Ast.Unknown
              "Lean backend: internal error — supply environment lost a declared supply"))
        (get_supply_params ())
    (* Bind the value×states tuple of a threaded control expression
       (if/match in pair form) to fresh names; returns the binding, the
       value output, and the refreshed environment. *)
    and supply_join senv (rhs : Output.t) =
      let v = supply_fresh_name "V" in
      let updates = List.map (fun (cref, _) -> (cref, supply_fresh_name "S")) (get_supply_params ()) in
      let bind = Output.flat
        ([from_string "let ("; from_string v]
         @ List.concat_map (fun (_, s) -> [from_string ", "; from_string s]) updates
         @ [from_string ") := ("; rhs; from_string ")"]) in
      (bind, SVar v, updates)
    (* An if/match ARM (or a def body) rendered to the pair form:
       (bindings; (value, final states)). *)
    and supply_arm inside_instance senv e =
      let (bs, v, senv') = supply_thread inside_instance senv e in
      let tup = Output.flat
        ([from_string "("; lean_sv_out v]
         @ List.concat_map (fun s -> [from_string ", "; from_string s]) (supply_state_names senv')
         @ [from_string ")"]) in
      Output.flat
        ([from_string "("]
         @ List.concat_map (fun b -> [b; from_string ";\n      "]) bs
         @ [tup; from_string ")"])
    (* Short-circuit threading: left operand
       strict, right operand as a branch arm of the equivalent if —
       draws in the right operand fire only when it evaluates. *)
    and supply_shortcircuit inside_instance senv (kind : string) le re =
      let (bs1, vl, senv1) = supply_thread inside_instance senv le in
      let arm_r = supply_arm inside_instance senv1 re in
      let const_arm b =
        Output.flat
          ([from_string "("; from_string b]
           @ List.concat_map (fun s -> [from_string ", "; from_string s])
               (supply_state_names senv1)
           @ [from_string ")"]) in
      let vl = lean_sv_out vl in
      let rhs =
        if kind = "&&" then
          Output.flat [from_string "lem_if "; vl; from_string " then "; arm_r;
                       from_string " else "; const_arm "false"]
        else
          Output.flat [from_string "lem_if "; vl; from_string " then "; const_arm "true";
                       from_string " else "; arm_r] in
      let (bind, v, senv') = supply_join senv1 rhs in
      (bs1 @ [bind], v, senv')
    (* Materialise threaded argument values as real `Var`
       expressions so the shared application renderer (target reps, ascii
       reps, renaming, paren insertion) can render an application whose
       arguments drew — it may REBUILD argument nodes (identifier-form
       reps inline to `App (Backend rep, args)`; mk_opt_paren_exp re-creates
       spines), which defeated the previous physical-identity substitution
       memo and left library-constructor arguments (`Just (fresh ())`)
       refused with a misleading message. A synthesized variable is used
       as-is; a compound threaded value is first bound to a fresh name
       (A-normal form). Pure arguments keep their original node. *)
    and supply_atomize_args (args : exp list) (vals : lean_sval list) : Output.t list * exp list =
      List.fold_right2 (fun a v (bs, es) ->
          if not (exp_needs_supply a) then (bs, a :: es)
          else begin
            let (bs', name) = (match v with
              | SVar n -> ([], n)
              | SPure o ->
                let n = supply_fresh_name "A" in
                ([Output.flat [from_string "let "; from_string n; from_string " := "; o]], n)) in
            let var = C.mk_var (Typed_ast.exp_to_locn a)
                (Name.add_lskip (Name.from_rope (Ulib.Text.of_string name)))
                (Typed_ast.exp_to_typ a) in
            (bs' @ bs, var :: es)
          end)
        args vals ([], [])
    (* Thread a node's subexpressions in OCaml order: the LAST element is
       evaluated first (right-to-left); the values come back in positional
       order, the bindings in evaluation order. *)
    and supply_thread_list inside_instance senv es =
      List.fold_right (fun e (bs, vs, senv) ->
          let (b, v, senv') = supply_thread inside_instance senv e in
          (bs @ b, v :: vs, senv'))
        es ([], [], senv)
    and supply_thread inside_instance senv (e : exp) =
      let l = Typed_ast.exp_to_locn e in
      let err msg = raise (Reporting_basic.err_general true l msg) in
      let pure_out e' =
        if needs_parens (C.exp_to_term e') then
          Output.flat [from_string "("; exp inside_instance e'; from_string ")"]
        else exp inside_instance e' in
      if not (exp_needs_supply e) then ([], SPure (pure_out e), senv)
      else match C.exp_to_term e with
      | Paren (_, e1, _) -> supply_thread inside_instance senv e1
      | Begin (_, e1, _) -> supply_thread inside_instance senv e1
      | Typed (_, e1, _, t, _) ->
        let (bs, v, senv') = supply_thread inside_instance senv e1 in
        (bs, SPure (Output.flat [from_string "("; lean_sv_out v; from_string " :"; pat_typ t; from_string ")"]), senv')
      | App _ -> supply_thread_app inside_instance senv e
      | Let (_, (lb, _), _, e2) ->
        (match lb with
         | Let_val (p, _, _, e1) when (lean_seq_pattern p || lean_seq_unused_binding p e2)
                                     && not (lean_seq_trivial e1)
                                     && not (exp_needs_supply e1) ->
           err "Lean backend: `let _ = e1 in e2` with a pure e1 in a supply-threaded body (e1 would be dropped; unsupported — bind e1 to a used name, or move it out of the supply-threaded region)"
         | Let_val (p, topt, _, e1) ->
           let (bs1, v1, senv1) = supply_thread inside_instance senv e1 in
           let p_out, topt_out = (match p.term with
             (* the P_typ unwrap of let_body: `let (x : T) := v` would
                pattern-match, not bind *)
             | P_typ (_, inner_p, _, t, _) ->
               def_pattern inner_p, Output.flat [from_string " :"; pat_typ t]
             | _ ->
               def_pattern p,
               (match topt with
                | None -> emp
                | Some (_, t) -> Output.flat [from_string " :"; pat_typ t])) in
           let bind = Output.flat [from_string "let "; p_out; topt_out; from_string " := "; lean_sv_out v1] in
           let (bs2, v2, senv2) = supply_thread inside_instance senv1 e2 in
           (bs1 @ (bind :: bs2), v2, senv2)
         | Let_fun _ ->
           err "Lean backend: unexpected Let_fun under supply threading (should have been compiled away)")
      | If (_, tst, _, et, _, ef) ->
        let (bs0, v0, senv0) = supply_thread inside_instance senv tst in
        let v0 = lean_sv_out v0 in
        if not (exp_needs_supply et || exp_needs_supply ef) then
          (bs0,
           SPure (Output.flat [from_string "(lem_if "; v0; from_string " then "; pure_out et;
                        from_string " else "; pure_out ef; from_string ")"]),
           senv0)
        else begin
          let armT = supply_arm inside_instance senv0 et in
          let armF = supply_arm inside_instance senv0 ef in
          let (bind, v, senv') = supply_join senv0
            (Output.flat [from_string "lem_if "; v0; from_string " then "; armT;
                          from_string " else "; armF]) in
          (bs0 @ [bind], v, senv')
        end
      | Case (_, _, e0, _, cases, _)
        when Seplist.length cases = 1 && not (lean_seq_trivial e0) && not (exp_needs_supply e0)
             && (let (p, _, _, _) = Seplist.hd cases in lean_seq_pattern p) ->
        err "Lean backend: `let () = e1 in e2` with a pure e1 in a supply-threaded body (e1 would be dropped; unsupported — bind e1 to a used name, or move it out of the supply-threaded region)"
      | Case (_, _, e0, _, cases, _) ->
        let (bs0, v0, senv0) = supply_thread inside_instance senv e0 in
        let v0 = lean_sv_out v0 in
        let arm_list = Seplist.to_list cases in
        if not (List.exists (fun (_, _, ea, _) -> exp_needs_supply ea) arm_list) then
          let arms = List.map (fun (p, _, ea, _) ->
              flatten_newlines (Output.flat
                [from_string "\n      | "; def_pattern p; from_string " => "; pure_out ea]))
            arm_list in
          (bs0,
           SPure (Output.flat ([from_string "(match "; v0; from_string " with"]
                        @ arms @ [from_string ")"])),
           senv0)
        else begin
          let arms = List.map (fun (p, _, ea, _) ->
              Output.flat [from_string "\n      | "; def_pattern p; from_string " => ";
                           supply_arm inside_instance senv0 ea])
            arm_list in
          let (bind, v, senv') = supply_join senv0
            (Output.flat ([from_string "match "; v0; from_string " with"] @ arms)) in
          (bs0 @ [bind], v, senv')
        end
      | Tup (_, es, _) ->
        let (bs, vs, senv') = supply_thread_list inside_instance senv (Seplist.to_list es) in
        (bs, SPure (Output.flat [from_string "("; Output.concat (from_string ", ") (List.map lean_sv_out vs); from_string ")"]), senv')
      | List (_, es, _) ->
        let (bs, vs, senv') = supply_thread_list inside_instance senv (Seplist.to_list es) in
        (bs, SPure (Output.flat [from_string "["; Output.concat (from_string ", ") (List.map lean_sv_out vs); from_string "]"]), senv')
      | Record (_, fields, _) ->
        let typ = Typed_ast.exp_to_typ e in
        (match mutual_record_path typ with
         | Some _ ->
           err "Lean backend: supply draw in a mutual-record construction (unsupported; bind the drawn values in lets before the construction)"
         | None ->
           let fl = Seplist.to_list fields in
           (* OCaml evaluates record fields in the type's FIELD DECLARATION
              order (right-to-left), whatever the source order of the
              construction; sort the fields accordingly before threading
              and render them back in source order (Lean's structure
              instance notation accepts any order). *)
           let decl_index =
             match Types.type_defs_lookup_typ Ast.Unknown A.env.t_env typ with
             | Some td ->
               (match td.Types.type_fields with
                | Some refs ->
                  (fun (fd : const_descr_ref id) ->
                    let rec go i = function
                      | [] -> err "Lean backend: internal error — record field missing from its type's field list under supply threading"
                      | r :: rs -> if r = fd.descr then i else go (i + 1) rs in
                    go 0 refs)
                | None -> err "Lean backend: internal error — record type without a field list under supply threading")
             | None -> err "Lean backend: internal error — record type not found under supply threading" in
           let indexed = List.mapi (fun i ((fd, _, _, _) as f) -> (decl_index fd, i, f)) fl in
           let by_decl = List.sort (fun (a, _, _) (b, _, _) -> Int.compare a b) indexed in
           let (bs, vs_decl, senv') =
             supply_thread_list inside_instance senv (List.map (fun (_, _, (_, _, ef, _)) -> ef) by_decl) in
           let vs_by_src = List.sort (fun ((_, i, _), _) ((_, j, _), _) -> Int.compare i j) (List.combine by_decl vs_decl) in
           let fields_out = List.map (fun ((_, _, (fd, _, _, _)), v) ->
               Output.flat [field_ident_to_output fd (use_ascii_rep_for_const fd.descr);
                            from_string " := "; lean_sv_out v])
             vs_by_src in
           let src_t = C.t_to_src_t typ in
           (bs,
            SPure (Output.flat [from_string "(({ "; Output.concat (from_string ", ") fields_out;
                         from_string " } : "; pat_typ src_t; from_string "))"]),
            senv'))
      | Field (e0, sk, fd) ->
        let (bs, v0, senv') = supply_thread inside_instance senv e0 in
        let name = field_ident_to_output fd (use_ascii_rep_for_const fd.descr) in
        (bs, SPure (Output.flat [lean_sv_out v0; from_string "."; ws sk; name]), senv')
      | Infix (le, ce, re) ->
        (match C.exp_to_term ce with
         | Constant cd when is_supply_cref cd.descr
                            || Types.Cdset.mem cd.descr !St.supply_lifted ->
           (* G-infix *)
           err "Lean backend: supply constant or supply-lifted definition used in infix position (unsupported; use prefix application so the call can be threaded)"
         | Constant cd when is_consumer_cref cd.descr ->
           err "Lean backend: reader_consumer used in infix position (unsupported: the leading reader arguments cannot be injected around an infix operator — use prefix application)"
         | Constant cd when lean_shortcircuit_kind cd.descr <> None
                            && exp_needs_supply re ->
           (* never hoist right-operand
              draws above a short-circuit test *)
           let kind = (match lean_shortcircuit_kind cd.descr with
             | Some k -> k
             | None ->
               err "Lean backend: internal error — short-circuit head lost its classification") in
           supply_shortcircuit inside_instance senv kind le re
         | Constant cd when lean_tuple_inst_demands A.env cd <> [] ->
           err "Lean backend: a confusable tuple-instance demand in a supply-threaded infix application (unsupported; bind the operands in lets first)"
         | Constant cd ->
           (* OCaml order: the RIGHT operand is evaluated first *)
           let (bs2, vr, senv1) = supply_thread inside_instance senv re in
           let (bs1, vl, senv2) = supply_thread inside_instance senv1 le in
           (* render via the pure Infix machinery with the drawing
              operands replaced by their threaded variables *)
           let (bs_a, ops) = supply_atomize_args [le; re] [vl; vr] in
           let pieces = B.function_application_to_output (exp_to_locn e) pure_out true e cd ops (use_ascii_rep_for_const cd.descr) in
           (bs2 @ bs1 @ bs_a,
            SPure (Output.flat [from_string "("; Output.concat (from_string " ") pieces; from_string ")"]),
            senv2)
         | _ ->
           let (bs2, vr, senv1) = supply_thread inside_instance senv re in
           let (bs1, vl, senv2) = supply_thread inside_instance senv1 le in
           (bs2 @ bs1,
            SPure (Output.flat [from_string "("; lean_sv_out vl; from_string " "; pure_out ce;
                         from_string " "; lean_sv_out vr; from_string ")"]),
            senv2))
      | Fun _ | Function _ ->
        (* G-λ: the honest boundary of the feature — a linear supply
           cannot be captured by a closure, and there is no
           partial-application repair (contrast the reader lifting). *)
        err "Lean backend: supply draw (or supply-lifted call) under a lambda (unsupported: a linear supply cannot be captured by a closure — restructure so the draw happens outside the lambda, or thread the state explicitly in the model)"
      | Do _ ->
        err "Lean backend: supply draw (or supply-lifted call) inside a do-block / monadic bind (unsupported: supply threading is first-order state-passing; a monadic region needs an explicit state component in the model)"
      | Quant _ | Setcomp _ | Comp_binding _ | Set _ ->
        err "Lean backend: supply draw in a set/comprehension/quantifier context (unsupported)"
      | Recup _ ->
        err "Lean backend: supply draw in a record-update expression (unsupported; bind the drawn values in lets before the update)"
      | Vector _ | VectorSub _ | VectorAcc _ ->
        err "Lean backend: supply draw in a vector expression (unsupported)"
      | Constant cd when is_supply_cref cd.descr ->
        err "Lean backend: bare (unapplied) reference to a supply constant (unsupported: apply it to () so the draw can be threaded)"
      | Constant cd when Types.Cdset.mem cd.descr !St.supply_lifted ->
        (* G-bare *)
        err "Lean backend: bare (unapplied) reference to a supply-lifted definition (unsupported: linear supply threading has no partial-application repair — apply it fully inside a lifted definition instead of passing it as a value)"
      | Var _ | Constant _ | Lit _ | Backend _ | Nvar_e _ ->
        ([], SPure (pure_out e), senv)
    and supply_thread_app inside_instance senv e =
      let l = Typed_ast.exp_to_locn e in
      let err msg = raise (Reporting_basic.err_general true l msg) in
      let pure_out e' =
        if needs_parens (C.exp_to_term e') then
          Output.flat [from_string "("; exp inside_instance e'; from_string ")"]
        else exp inside_instance e' in
      let (e0, args) = strip_app_exp e in
      match C.exp_to_term e0 with
      | Constant cd when is_supply_cref cd.descr ->
        (* THE DRAW: let (v, s') := LemLib.supplySplit s *)
        if List.length args <> 1 then
          (* G-arity *)
          err "Lean backend: a supply constant must be applied to exactly one (unit) argument (the draw rewrite replaces the whole application spine)";
        if exp_needs_supply (List.hd args) then
          err "Lean backend: the unit argument of a supply draw itself uses the supply (unsupported; sequence the draws in lets)";
        let scur = (match List.assoc_opt cd.descr senv with
          | Some s -> s
          | None ->
            err "Lean backend: internal error — supply constant missing from the threading environment") in
        let v = supply_fresh_name "V" in
        let s' = supply_fresh_name "S" in
        let bind = Output.flat
          [from_string "let ("; from_string v; from_string ", "; from_string s';
           from_string ") := LemLib.supplySplit "; from_string scur] in
        let senv' = List.map (fun (c, s) ->
            if c = cd.descr then (c, s') else (c, s)) senv in
        ([bind], SVar v, senv')
      | Constant cd when Types.Cdset.mem cd.descr !St.supply_lifted ->
        (* THREADED CALL of a lifted def: bind the value×states pair. *)
        let arity = supply_arity_of cd.descr in
        if List.length args <> arity then
          err (Printf.sprintf
            "Lean backend: supply-lifted definition applied to %d argument(s) where its threading arity is %d (unsupported: linear supply threading requires exact full application — no partial application, no extra arguments on the returned value)"
            (List.length args) arity);
        let (bs, argvs, senv1) = supply_thread_list inside_instance senv args in
        (* head render: the existing bare-Constant machinery (fuel-worker
           rewrite, reader partial application, renaming) with the
           supply net suppressed for exactly this render *)
        let head =
          let saved = !St.supply_head_ok in
          St.supply_head_ok := true;
          Fun.protect ~finally:(fun () -> St.supply_head_ok := saved)
            (fun () -> pure_out e0) in
        let scurs = supply_state_names senv1 in
        let call = Output.flat
          ([head]
           @ List.concat_map (fun s -> [from_string " "; from_string s]) scurs
           @ List.concat_map (fun a -> [from_string " "; lean_sv_out a]) argvs) in
        let (bind, v, senv2) = supply_join senv1 call in
        (bs @ [bind], v, senv2)
      | Constant cd when (match lean_shortcircuit_kind cd.descr, args with
                          | Some _, [_; b] -> exp_needs_supply b
                          | Some _, _ -> List.exists exp_needs_supply args
                          | None, _ -> false) ->
        (* short-circuit operator reached as an application spine:
           same arm-threading as the Infix leg when
           fully applied; anything else fails closed *)
        (match args with
         | [a; b] ->
           let kind = (match lean_shortcircuit_kind cd.descr with
             | Some k -> k
             | None ->
               err "Lean backend: internal error — short-circuit head lost its classification") in
           supply_shortcircuit inside_instance senv kind a b
         | _ ->
           err "Lean backend: supply draw in an argument of a partially or over-applied short-circuit operator (&& / ||) (unsupported; apply the operator to exactly two operands)")
      | Constant cd when is_consumer_cref cd.descr ->
        (* reader_consumer head with supply-using arguments: hoist the
           arguments, render the head through the bare-Constant
           consumer branch (reader injection + scope check), apply. *)
        let (bs, argvs, senv1) = supply_thread_list inside_instance senv args in
        (bs,
         SPure (Output.flat ([from_string "("; pure_out e0]
                      @ List.concat_map (fun a -> [from_string " "; lean_sv_out a]) argvs
                      @ [from_string ")"])),
         senv1)
      | Constant cd ->
        (* pure head with supply-using arguments: hoist the arguments in
           OCaml order (right-to-left), then render the application through the ordinary
           machinery (target reps, ascii reps, renaming) with the
           argument nodes substituted by their threaded values. The
           special head classes cannot take hoisted arguments soundly
           and fail closed. *)
        lean_unsupported_check_cref A.env l cd.descr;
        if lean_tuple_inst_demands A.env cd <> [] then
          err "Lean backend: a confusable tuple-instance demand in a supply-threaded application (unsupported; bind the drawn values in lets first)";
        if is_lean_failwith_rep cd.descr then
          err "Lean backend: a failwith-mapped call with supply-drawing arguments (unsupported; bind the drawn values in lets first)";
        if ground_rep_for cd.descr <> None then
          err "Lean backend: a ground_rep-mapped call with supply-drawing arguments (unsupported; bind the drawn values in lets first)";
        if is_reader_cref cd.descr then
          err "Lean backend: internal error — a reader constant's unit argument cannot use the supply";
        let (bs, argvs, senv1) = supply_thread_list inside_instance senv args in
        (* drawing arguments become real variables (see supply_atomize_args) *)
        let (bs_a, args') = supply_atomize_args args argvs in
        let pieces = B.function_application_to_output (exp_to_locn e) pure_out false e cd args' (use_ascii_rep_for_const cd.descr) in
        (bs @ bs_a,
         SPure (Output.flat [from_string "("; Output.concat (from_string " ") pieces; from_string ")"]),
         senv1)
      | _ ->
        (* general head (variable, threaded subexpression, ...): every
           argument and then the head are hoisted — STRICT threading in
           OCaml order.
           NOTE: PAREN-WRAPPED
           heads land here too, because strip_app_exp
           (typed_ast_syntax.ml) deliberately does not unwrap Paren.
           In particular the paren-split short-circuit spine
           `((&&) a) (chk 4)` bypasses the shortcircuit leg above and
           threads its argument STRICTLY. That is ORACLE-FAITHFUL —
           OCaml evaluates the argument of the eta-expanded form
           strictly as well, while the flat `a && chk 4` form
           short-circuits on both targets — but the case-for-case
           match rests on lem's Paren node coinciding with OCaml's
           full-application detection, which is a coincidence of
           representation, not a theorem. The behavior is
           kernel-pinned (tests/comprehensive/test_supply.lem
           prefsc_paren + TestSupplyCheck.lean): any future spine
           normalization that unwraps Paren will change the threading
           class of such spines and MUST re-adjudicate those pins
           against the oracle, not just update them. *)
        (* OCaml order: the arguments (right-to-left), THEN the head *)
        let (bs, argvs, senv0) = supply_thread_list inside_instance senv args in
        let (bs0, v0, senv1) = supply_thread inside_instance senv0 e0 in
        (bs @ bs0,
         SPure (Output.flat ([from_string "("; lean_sv_out v0]
                      @ List.concat_map (fun a -> [from_string " "; lean_sv_out a]) argvs
                      @ [from_string ")"])),
         senv1)
    (* A supply-lifted def BODY: bindings then the value×states tuple,
       threading from the binder names. *)
    and supply_block inside_instance (e : exp) : Output.t =
      St.supply_name_counter := 0;
      let senv0 = List.map (fun (cref, pname) -> (cref, pname)) (get_supply_params ()) in
      let (bs, v, senv') = supply_thread inside_instance senv0 e in
      let tup = Output.flat
        ([from_string "("; lean_sv_out v]
         @ List.concat_map (fun s -> [from_string ", "; from_string s]) (supply_state_names senv')
         @ [from_string ")"]) in
      Output.flat
        ([from_string "\n  "]
         @ List.concat_map (fun b -> [b; from_string ";\n  "]) bs
         @ [tup])
    and supply_binder_output () =
      if not !St.supply_binder then emp else
      Output.flat (List.map (fun (_, pname) ->
          Output.flat [from_string " ("; from_string pname; from_string " : Nat)"])
        (get_supply_params ()))
    (* The threaded result-type suffix: × Nat per supply, in param order. *)
    and supply_pair_suffix () =
      Output.flat (List.map (fun _ -> from_string " × Nat") (get_supply_params ()))
    (* The full threaded arrow type of a lifted def (used by the fuel
       wrapper): its parameter types, then the result wrapped into the
       value×supply pair. *)
    and supply_transformed_typ_output (cd : const_descr) (npats : int) =
      let rec split n t =
        if n = 0 then ([], t)
        else match t.Types.t with
          | Types.Tfn (a, b) -> let (rest, r) = split (n - 1) b in (a :: rest, r)
          | _ ->
            raise (Reporting_basic.err_general true Ast.Unknown
              "Lean backend: internal error — supply-lifted def has more parameters than its type has arrows") in
      let (arg_ts, r) = split npats cd.const_type in
      Output.flat
        (List.concat_map (fun a ->
             [from_string "("; pat_typ (C.t_to_src_t a); from_string ") -> "]) arg_ts
         @ [from_string "(("; pat_typ (C.t_to_src_t r); from_string ")";
            supply_pair_suffix (); from_string ")"])

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
                    | _ ->
                      let method_name = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip n)) in
                      raise (Reporting_basic.err_general true Ast.Unknown
                        (String.concat "" ["Lean backend: instance method not found for '"; method_name; "'"]))
              end
        else begin
          lean_symbolic_def_check c;
          B.const_ref_to_name n true c
        end
      in
        funcl_aux inside_instance i_ref_opt constraints tv_set (n, pats, typ_opt, skips, e)
    and let_type_variables top_level tv_set =
      if Types.TNset.is_empty tv_set || not top_level then
        emp
      else
      (* consecutive variables of one kind share a binder, `{a b : Type}`;
         the order of the implicit arguments is unchanged *)
      let named = List.map (fun tv -> match tv with
          | Types.Ty tv -> ("Type", id Type_var (r (lean_tyvar_text (Ulib.Text.to_string (Tyvar.to_rope tv)))))
          | Types.Nv nv -> ("Nat", id Type_var (Nvar.to_rope nv)))
          (Types.TNset.elements tv_set) in
      let rec group = function
        | [] -> []
        | (k, v) :: rest ->
          (match group rest with
           | (k', vs) :: groups when k' = k -> (k, v :: vs) :: groups
           | groups -> (k, [v]) :: groups)
      in
      let bindings = List.map (fun (k, vs) ->
          Output.flat [from_string "{"; concat_str " " vs; from_string " : "; from_string k; from_string "}"])
          (group named)
      in
        from_string " " ^ concat_str " " bindings
    (* Expression rendering. Lean 4 parser-specific rules:
       - Match/if/let/fun in function args or case bodies are parenthesized
         (Lean's greedy rightward match would otherwise consume too much)
       - In indreln antecedents (St.prop_equality), == and != become = and ≠
       - For polymorphic indreln self-references (St.indreln_params), explicit
         type parameters are inserted since Lean can't infer them
       - Class method constants get explicit @ type application when used bare *)
    (* Sequencing: `lemSeq (fun _ => e1) (fun _ => e2)` *)
    and lem_seq_out inside_instance skips e1 e2 =
      let e1_out = exp inside_instance e1 in
      Output.flat [
        ws skips; from_string "(lemSeq (fun _ => "; e1_out;
        from_string ") (fun _ => "; exp inside_instance e2; from_string "))"
      ]

    (* A node headed by a constant whose class constraints reach a
       confusable tuple type binds Lem's instances locally first. *)
    and exp inside_instance e =
      (* The comments in front of an expression are taken out of its skips and
         emitted ahead of it, so no rendering path (rewrites, failure
         threading, pattern compilation) can drop them. The whitespace stays
         in place: the token spacing is unchanged. *)
      let out = match Typed_ast.alter_init_lskips take_comments e with
        | (_, None) -> exp_core inside_instance e
        | (e', lead_comments) -> Output.flat [inline_comments lead_comments; exp_core inside_instance e']
      in
      match lean_exp_head_const e with
      | None -> out
      | Some c ->
        (match lean_tuple_inst_demands A.env c with
         | [] -> out
         | ds ->
           let l = exp_to_locn e in
           let binding (inst, subst, _ty) =
             let args = List.map (fun tv ->
               match tv with
               | Types.Nv _ ->
                 raise (Reporting_basic.err_general true l
                   "Lean backend: tuple instance with a numeric type variable (unsupported for local instance binding)")
               | Types.Ty _ ->
                 (match Types.TNfmap.apply subst tv with
                  | Some t ->
                    Output.flat [from_string " ("; from_string (tnvar_name tv); from_string " := ";
                                 pat_typ (C.t_to_src_t t); from_string ")"]
                  | None ->
                    raise (Reporting_basic.err_general true l
                      "Lean backend: internal error — tuple instance variable not instantiated")))
               inst.Types.inst_tyvars in
             Output.flat ([from_string "haveI := "; from_string (lean_tuple_inst_name A.env inst)]
                          @ args @ [from_string "; "]) in
           Output.flat ([from_string "("] @ List.map binding ds @ [out; from_string ")"]))

    and exp_core inside_instance e =
        match C.exp_to_term e with
          | Var v ->
              name_var_output v
          | Backend (sk, i) ->
              if String.trim (Ident.to_string i) = "sorry" then
                raise (lean_sorry_rep_error (exp_to_locn e) "backend expression");
              ws sk ^
              Ident.to_output (Term_const (false, true)) path_sep i
          | Lit l -> literal l
          | Do (skips, _mod_descr_id, do_line_list, _skips', e, _skips'', _type_int) ->
              let lines = List.map (fun (Do_line (p, _s1, body, _s2)) ->
                let (body', _) = Typed_ast.alter_init_lskips (fun sk -> (Typed_ast.no_lskips, sk)) body in
                Output.flat [
                  from_string "    let "; fun_pattern p; from_string " ← "; exp inside_instance body'; from_string "\n"
                ]
              ) do_line_list in
              let (e', _) = Typed_ast.alter_init_lskips (fun sk -> (Typed_ast.no_lskips, sk)) e in
              Output.flat [
                ws skips; from_string "(do\n";
                concat emp lines;
                from_string "    "; exp inside_instance e'; from_string "\n";
                from_string "  )"
              ]
          | App (e1, e2) ->
              let trans e_inner =
                if needs_parens (C.exp_to_term e_inner) then
                  Output.flat [from_string "("; exp inside_instance e_inner; from_string ")"]
                else exp inside_instance e_inner
              in
              let sep = from_string " " in
              let oL = begin
              let (e0, args) = strip_app_exp e in
                match C.exp_to_term e0 with
                  | Constant cd ->
                    let c_descr = c_env_lookup Ast.Unknown A.env.c_env cd.descr in
                    (* supply net: threaded constants only render inside
                       the supply transform (guards G-rel and the
                       unliftable-context class) *)
                    lean_unsupported_check_cref A.env (Typed_ast.exp_to_locn e) cd.descr;
                    supply_net_check (Typed_ast.exp_to_locn e) cd.descr
                      "an application outside a supply-lifted definition body (instance method, indreln rule, lemma/assert, or another context the pre-pass cannot lift)";
                    fuel_scope_check (Typed_ast.exp_to_locn e) cd.descr "an application";
                    ireader_scope_check (Typed_ast.exp_to_locn e) cd.descr "an application";
                    (* In indreln antecedents (Prop context), == and != applied via
                       App nodes (e.g. from <> decomposition: not (isEqual x y)) must
                       use propositional =/≠ instead of BEq ==/!=. *)
                    let raw_output = begin match !St.prop_equality, args, check_beq_target_rep c_descr with
                    | true, [arg0; arg1], Some is_eq ->
                      let l_out = trans arg0 in
                      let r_out = trans arg1 in
                      if is_eq then [Output.flat [l_out; from_string "  =  "; r_out]]
                      else [Output.flat [l_out; meta_utf8 "  \xe2\x89\xa0  "; r_out]]
                    | _ ->
                      let is_fuel_self =
                        (* only while rendering a fuel'd body: elsewhere the
                           lemFuel binder is not in scope *)
                        !St.fuel_emit <> None
                        && List.mem_assoc cd.descr !St.fuel_workers in
                      if is_fuel_self then
                        (* Self-call in a fuel'd worker: 'trans e0' reaches the
                           bare-Constant case, which rewrites to
                           '(worker lemFuel)'; apply the original arguments. *)
                        let func_out = trans e0 in
                        let args_out = List.map trans args in
                        [Output.flat (func_out
                          :: List.map (fun a -> Output.flat [from_string " "; a]) args_out)]
                      else if is_ireader_cref cd.descr then begin
                        (* Application of an INSTANCE reader: 'r ()' becomes
                           the class projection; the unit-argument guard is
                           the explicit reader's (the rewrite replaces the
                           whole spine). *)
                        if List.length args <> 1 then
                          raise (Reporting_basic.err_general true
                            (Typed_ast.exp_to_locn e)
                            "Lean backend: an instance reader must be applied to exactly one (unit) argument (the rewrite replaces the whole application spine)");
                        [ireader_read_output cd.descr]
                      end
                      else if is_reader_cref cd.descr then begin
                        (* Application of the reader constant itself: 'tagDefs ()'
                           becomes the reader parameter. The only argument is
                           unit — CHECKED: the rewrite
                           replaces the whole application spine, so a reader
                           constant of arity beyond `unit -> T` applied to
                           extra arguments would silently DROP them; the
                           assumption is now a guard, not luck. *)
                        if List.length args <> 1 then
                          raise (Reporting_basic.err_general true
                            (Typed_ast.exp_to_locn e)
                            "Lean backend: a reader constant must be applied to exactly one (unit) argument (the rewrite replaces the whole application spine)");
                        [from_string (reader_inject_name (reader_param_name cd.descr))]
                      end
                      else if is_consumer_cref cd.descr then
                        (* reader_consumer call: 'trans e0' reaches the
                           bare-Constant case, which passes the reader
                           parameters (seed-name override included)
                           exactly once; apply the original arguments
                           after them. *)
                        let func_out = trans e0 in
                        let args_out = List.map trans args in
                        [Output.flat (func_out
                          :: List.map (fun a -> Output.flat [from_string " "; a]) args_out)]
                      else if ground_rep_for cd.descr <> None
                              && Types.TNset.is_empty (Types.free_vars (Typed_ast.exp_to_typ e)) then
                        (* Ground-typed site of a ground_rep constant:
                           swap the head, keep the arguments, ascribe the
                           type so the instance resolves exactly here. *)
                        let rep = match ground_rep_for cd.descr with
                          | Some r -> r | None -> assert false in
                        let args_out = List.map trans args in
                        [Output.flat ([from_string "(("; from_string rep; from_string ")"]
                          @ List.map (fun a -> Output.flat [from_string " "; a]) args_out
                          @ [from_string " : "; pat_typ (C.t_to_src_t (Typed_ast.exp_to_typ e)); from_string ")"])]
                      else if is_lean_failwith_rep cd.descr && args <> [] then begin
                        (* Failure site (EVERY site, ground or tyvar-typed):
                           axiom-free failwithI, with an ascription so the
                           instance resolves at exactly this type. Tyvar
                           sites resolve through the derived instances
                           and/or the [Inhabited tv]
                           binders threaded onto the enclosing def. *)
                        let site_t = Typed_ast.exp_to_typ e in
                        failwith_instance_guard inside_instance site_t;
                        [Output.flat ([from_string "(failwithI"]
                          @ List.map (fun a -> Output.flat [from_string " "; trans a]) args
                          @ [from_string " : "; pat_typ (C.t_to_src_t site_t);
                             from_string ")"])]
                      end
                      else if Types.Cdset.mem cd.descr !St.reader_lifted then
                        (* Call of a lifted def: `trans e0` reaches the bare-
                           Constant case, which injects the reader parameters
                           exactly once; just apply the original arguments. *)
                        let func_out = trans e0 in
                        let args_out = List.map trans args in
                        [Output.flat (func_out
                          :: List.map (fun a -> Output.flat [from_string " "; a]) args_out)]
                      else
                      begin match List.assoc_opt cd.descr !St.indreln_params with
                      | Some params_str ->
                        let func_out = trans e0 in
                        let args_out = List.map trans args in
                        [Output.flat ([func_out; from_string " "; from_string params_str]
                          @ List.map (fun a -> Output.flat [from_string " "; a]) args_out)]
                      | None ->
                        B.function_application_to_output (exp_to_locn e) trans false e cd args (use_ascii_rep_for_const cd.descr)
                      end
                    end in
                    raw_output
                  | Backend (_, i) when Ident.to_string i = "sorry" ->
                    raise (lean_sorry_rep_error (exp_to_locn e) "applied backend expression")
                  | _ ->
                    List.map trans (e0 :: args)
              end in
              Output.concat sep oL
          | Paren (skips, e, skips') ->
              Output.flat [
                ws skips; from_string "("; exp inside_instance e; ws skips'; from_string ")";
              ]
          | Typed (skips, e, skips', t, skips'') ->
              Output.flat [
                ws skips; from_string "("; exp inside_instance e; from_string " :"; ws skips'; pat_typ t; ws skips''; from_string ")";
              ]
          | Tup (skips, es, skips') ->
              let tups = flat @@ Seplist.to_sep_list (exp inside_instance) (sep (from_string ",")) es in
                Output.flat [
                  ws skips; from_string "("; tups; from_string ")"; ws skips'
                ]
          (* An empty list literal whose Lem type is closed is ascribed with
             it, wherever it occurs (an earlier rule applied only inside a
             discarded `let _ = e1`): a target rep
             more general than its Lem type (Cerberus's `print_debug_pure :
             Nat -> List d -> ...` for Lem's `list domain`; `List.length` for
             a `list bool -> nat`) otherwise leaves the element type unsolved
             whenever the surrounding term does not determine it -- in a
             discarded e1, but equally in `let y = f [] in ...`. Ascribing the
             whole discarded e1 instead does not help (measured: its result
             type does not mention the unsolved parameter). Elaboration-only:
             the kernel term is the same `@List.nil T`. *)
          | List (skips, es, skips')
            when Seplist.length es = 0
                 && Types.TNset.is_empty (Types.free_vars (Typed_ast.exp_to_typ e)) ->
              Output.flat [
                ws skips; from_string "([] : "; pat_typ (C.t_to_src_t (Typed_ast.exp_to_typ e));
                from_string ")"; ws skips'
              ]
          | List (skips, es, skips') ->
              let lists = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun _ -> from_string " ")) (exp inside_instance) (sep @@ from_string ",") es in
                Output.flat [
                  ws skips; from_string "["; lists; from_string "]"; ws skips'
                ]
          | Let (skips, (Let_val (p, _, _, e1), _), _skips', e)
            when (lean_seq_pattern p || lean_seq_unused_binding p e) && not (lean_seq_trivial e1) ->
              lem_seq_out inside_instance skips e1 e
          | Let (skips, bind, _skips', e) ->
              let body = flatten_newlines (let_body inside_instance None false Types.TNset.empty bind) in
                Output.flat [
                  ws skips; from_string "let "; body; from_string "; "; exp inside_instance e
                ]
          | Constant const ->
              let c_descr = c_env_lookup Ast.Unknown A.env.c_env const.descr in
              (* supply net: a bare threaded constant outside the supply
                 transform is guard G-bare (no partial-application
                 repair exists for a linear supply) *)
              lean_unsupported_check_cref A.env (Typed_ast.exp_to_locn e) const.descr;
              supply_net_check (Typed_ast.exp_to_locn e) const.descr
                "a bare (unapplied) reference outside a supply-lifted definition body";
              fuel_scope_check (Typed_ast.exp_to_locn e) const.descr "a bare (unapplied) reference";
              ireader_scope_check (Typed_ast.exp_to_locn e) const.descr "a bare (unapplied) reference";
              let default_const_output () =
                Output.concat emp (B.function_application_to_output (exp_to_locn e) (exp inside_instance) false e const [] (use_ascii_rep_for_const const.descr))
              in
              begin match (if !St.fuel_emit = None then None
                           else List.assoc_opt const.descr !St.fuel_workers) with
              | Some w ->
                (* Self- or cross-member call inside a fuel'd block: recurse
                   on the decremented fuel binder; a lifted worker also
                   re-injects its reader binders. *)
                let readers =
                  if !St.reader_binder then reader_args_output () else emp in
                Output.flat [from_string "("; from_string w;
                             from_string " lemFuel"; readers; from_string ")"]
              | None ->
              if is_ireader_cref const.descr then
                (* Bare reference to an instance reader: eta-expand so the
                   unit-function type is preserved. *)
                Output.flat [from_string "(fun (_ : Unit) => ";
                             ireader_read_output const.descr; from_string ")"]
              else if is_reader_cref const.descr then
                (* Bare reference to the reader constant (unapplied):
                   eta-expand so the unit-function type is preserved. *)
                Output.flat [from_string "(fun (_ : Unit) => ";
                             from_string (reader_inject_name (reader_param_name const.descr)); from_string ")"]
              else if is_consumer_cref const.descr then begin
                (* reader_consumer: partially apply the reader
                   parameters onto the rep (type-preserving — the
                   hand-written implementation takes them as leading
                   parameters), which repairs bare/HOF references and
                   serves as the injected head of applied calls. *)
                reader_consumer_scope_check (Typed_ast.exp_to_locn e);
                Output.flat [from_string "("; default_const_output ();
                             reader_args_output (); from_string ")"]
              end
              else if Types.Cdset.mem const.descr !St.reader_lifted then
                (* Bare reference to a lifted def (e.g. passed to a HOF):
                   partially apply the reader parameters. *)
                Output.flat [from_string "("; default_const_output ();
                             reader_args_output (); from_string ")"]
              else if is_lean_failwith_rep const.descr then begin
                (* Bare / point-free failure reference: the
                   ascription (String -> tau) determines failwithI's
                   type argument; Inhabited tau resolves as at applied
                   sites. Legacy failwith is never emitted. *)
                let site_t = Typed_ast.exp_to_typ e in
                failwith_instance_guard inside_instance site_t;
                Output.flat [from_string "(failwithI : ";
                             pat_typ (C.t_to_src_t site_t); from_string ")"]
              end
              else
              (* Class method constants used bare (no explicit arguments) need explicit
                 @ type application in Lean 4. Without it, Lean can't infer the class
                 type parameter for nullary methods like `size : {a : Type} → [Size a] → Nat`
                 because the return type `Nat` doesn't mention the type parameter `a`.
                 Using `@size a _` provides the type argument explicitly.
                 Skip this for class methods that have a Lean target rep, since the
                 target rep already handles resolution. *)
              if c_descr.const_class <> [] then begin
                match Target.Targetmap.apply_target c_descr.target_rep
                        (Target.Target_no_ident Target.Target_lean) with
                | Some _ -> default_const_output ()
                | None ->
                  let i = B.const_id_to_ident const false in
                  let sk = Ident.get_lskip i in
                  let type_args = List.map (fun t ->
                    let src_t = C.t_to_src_t t in
                    Output.flat [from_string " ("; pat_typ src_t; from_string ")"]
                  ) const.instantiation in
                  (* + the threaded comparison binders (lean_cmp_prepass) *)
                  let num_classes = List.length c_descr.const_class
                    + List.length (Option.value ~default:[] (Hashtbl.find_opt St.lean_cmp_bounds const.descr)) in
                  let class_holes = List.init num_classes (fun _ -> from_string " _") in
                  (* Parenthesize the @name (type) _ expression so it can safely
                     appear as an argument to another function *)
                  Output.flat ([ws sk; from_string "(@"; Ident.to_output (Term_const (false, true)) path_sep (Ident.replace_lskip i no_lskips)] @ type_args @ class_holes @ [from_string ")"])
              end else
                default_const_output ()
              end
          | Fun (skips, ps, skips', e) ->
              let ps = fun_pattern_list inside_instance ps in
                Output.flat [
                  ws skips; from_string "fun"; ps; ws skips'; from_string "=> "; exp inside_instance e
                ]
          | Function _ ->
              print_and_fail (Typed_ast.exp_to_locn e) "illegal function in extraction, should have been previously macro'd away"
          | Set (skips, es, skips') ->
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun _ -> emp)) (exp inside_instance) (sep @@ from_string ", ") es in
            let skips =
              if skips = Typed_ast.no_lskips then
                from_string " "
              else
                ws skips
            in
              if Seplist.is_empty es then
                Output.flat [
                  skips; from_string "(setEmpty)"
                ]
              else
                (* A set literal is deduplicated by the SetType comparator,
                   as the OCaml target's comparator-keyed Pset is — never by
                   BEq: a BEq finer than the comparator (Cerberus's symbols)
                   could otherwise keep comparator-equal duplicates. The lem
                   type of a set literal carries SetType 'a, so the instance
                   is resolvable at every splice site. *)
                Output.flat [
                  skips; from_string "(setFromListBy setElemCompare ["; body; from_string "])"; ws skips'
                ]
          | Begin (skips, e, skips') ->
              (* Lem's begin...end is a grouping construct. In Lean, use parens. *)
              Output.flat [
                ws skips; from_string "("; exp inside_instance e; ws skips';
                from_string ")"
              ]
          | Record (skips, fields, skips') ->
            let typ = Typed_ast.exp_to_typ e in
            (match mutual_record_path typ with
            | Some path ->
              (* Mutual records are rendered as inductives, not structures.
                 Use constructor syntax: TypeName.mk val1 val2 ...
                 The `mk` arguments are POSITIONAL in the type's field
                 DECLARATION order; the literal may list its fields in any
                 order (linksem's dwarf.lem: the sdt_subroutine
                 literal lists ss_unspecified_parameters before ss_pc_ranges;
                 emitting in literal order was a type error there, and a
                 SILENT field swap wherever the swapped fields share a type). *)
              let field_vals = Seplist.to_list fields in
              let decl_fields =
                match Types.type_defs_lookup_typ Ast.Unknown A.env.t_env typ with
                | Some { Types.type_fields = Some fs; _ } -> fs
                | _ ->
                  raise (Reporting_basic.err_general true (Typed_ast.exp_to_locn e)
                    "Lean backend: mutual record literal: could not find the record type's field list")
              in
              if List.length decl_fields <> List.length field_vals then
                raise (Reporting_basic.err_general true (Typed_ast.exp_to_locn e)
                  "Lean backend: mutual record literal does not give every field exactly once");
              let vals = List.map (fun f_ref ->
                match List.find_opt (fun (fd, _, _, _) -> fd.descr = f_ref) field_vals with
                | Some (_, _, e_val, _) ->
                  Output.flat [from_string " ("; exp inside_instance e_val; from_string ")"]
                | None ->
                  raise (Reporting_basic.err_general true (Typed_ast.exp_to_locn e)
                    "Lean backend: mutual record literal is missing a declared field")
              ) decl_fields in
              let n0 = Name.add_lskip (Path.get_name path) in
              let n = B.type_path_to_name n0 path in
              let type_name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip n)) in
              Output.flat ([
                ws skips; from_string "("; from_string type_name_str; from_string ".mk"
              ] @ vals @ [
                ws skips'; from_string ")"
              ])
            | None ->
              let body = flatten_newlines (flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun _ -> emp)) (field_update inside_instance) (sep @@ from_string ",") fields) in
              (* Add type ascription so Lean can resolve the record type from
                 field names. Without it, { field := value } fails when the
                 expected type isn't known from context (e.g., in a let binding). *)
              let src_t = C.t_to_src_t typ in
                Output.flat [
                  ws skips; from_string "(({ "; body; ws skips'; from_string " } : "; pat_typ src_t; from_string "))"
                ]
            )
          | Field (e, skips, fd) ->
            let name = field_ident_to_output fd (use_ascii_rep_for_const fd.descr) in
            (* Dot notation works for both structures (.field accessor) and
               mutual records (we generate explicit accessor functions).
               Parenthesize match/if/let/fun: without parens, .field binds
               to the last arm body, not the whole expression. *)
            let e_out =
              if needs_parens (C.exp_to_term e) then
                Output.flat [from_string "("; exp inside_instance e; from_string ")"]
              else exp inside_instance e
            in
              Output.flat [
                e_out; from_string "."; ws skips; name
              ]
          | Recup (skips, e, skips', fields, skips'') ->
            let e_typ = Typed_ast.exp_to_typ e in
            (match mutual_record_path e_typ with
            | Some path ->
              (* Mutual records are inductives — { r with ... } doesn't work.
                 Look up all fields from the type definition, reconstruct with
                 accessor functions for unchanged fields and new values for updated ones. *)
              let updated = Seplist.to_list fields in
              let updated_names = List.map (fun (fd, _, _, _) ->
                let c_descr = c_env_lookup Ast.Unknown A.env.c_env fd.descr in
                Name.to_string (Path.get_name c_descr.const_binding)
              ) updated in
              let updated_map = List.map2 (fun name (_, _, e_val, _) -> (name, e_val)) updated_names updated in
              (* The base is bound ONCE, `(let lemRecBase := e; T.mk v1
                 lemRecBase.f2 …)`: it used to be re-rendered per unchanged
                 field, unparenthesised — `<| mk n with f = 5 |>` came out as
                 `(r.mk 5 (mk n.g))`, which Lean reads as `mk (n.g)` — and
                 evaluated once per field. The binder is a reserved name
                 (lean_reserved_exact_names): a free variable or a referenced
                 constant of that name in the base or an updated value would
                 be captured, so it is refused. *)
              let base = lean_reserved_rec_base_name in
              let locn = Typed_ast.exp_to_locn e in
              let capture_check (e' : exp) =
                Nfmap.iter (fun n _ ->
                    if Name.to_string n = base then
                      raise (Reporting_basic.err_general true locn
                        (Printf.sprintf "Lean backend: variable '%s' is the reserved binder of a mutual-record update (the reserved-name contract) — rename the variable" base)))
                  (C.exp_to_free e');
                lean_reserved_capture_check A.env locn "record update" e' in
              capture_check e;
              List.iter (fun (_, _, e_val, _) -> capture_check e_val) updated;
              (* Look up the type's fields from the environment *)
              (match Types.type_defs_lookup_typ Ast.Unknown A.env.t_env e_typ with
                | Some td ->
                  let all_fields = match td.Types.type_fields with
                    | Some fs -> fs | None -> [] in
                  let field_vals = List.map (fun f_ref ->
                    let c_descr = c_env_lookup Ast.Unknown A.env.c_env f_ref in
                    let fname = Name.to_string (
                      Path.get_name c_descr.const_binding) in
                    match List.assoc_opt fname updated_map with
                      | Some e_val -> Output.flat [from_string " ("; exp inside_instance e_val; from_string ")"]
                      | None -> Output.flat [from_string " "; from_string base; from_string "."; from_string (lean_escape_keyword fname)]
                  ) all_fields in
                  let n0 = Name.add_lskip (Path.get_name path) in
                  let n = B.type_path_to_name n0 path in
                  let type_name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip n)) in
                  Output.flat ([
                    ws skips; from_string "(let "; from_string base; from_string " := "; exp inside_instance e;
                    from_string "; "; from_string type_name_str; from_string ".mk"
                  ] @ field_vals @ [
                    from_string ")"
                  ])
                | None ->
                  raise (Reporting_basic.err_general true (Typed_ast.exp_to_locn e)
                    "Lean backend: mutual record update could not find type definition")
              )
            | None ->
              let body = flatten_newlines (flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun _ -> emp)) (field_update inside_instance) (sep @@ from_string ",") fields) in
              let skips'' =
                if skips'' = Typed_ast.no_lskips then
                  from_string " "
                else
                  ws skips''
              in
                Output.flat [
                   ws skips; from_string "{ "; exp inside_instance e; ws skips'; from_string " with "; body; skips''; from_string " }"
                ]
            )
          | Case (_, skips, e1, _, cases, _)
            when Seplist.length cases = 1 && not (lean_seq_trivial e1)
                 && (let (p, _, _, _) = Seplist.hd cases in lean_seq_pattern p) ->
            (* `let () = e1 in e2` reaches the backend as a one-arm
               match; OCaml evaluates the scrutinee for its effect *)
            let (_, _, e2, _) = Seplist.hd cases in
            lem_seq_out inside_instance skips e1 e2
          | Case (_, skips, e, skips', cases, skips'') ->
            let case_sep sk = Output.flat [from_string " "; inline_comments sk] in
            let has_vec = Seplist.exists (fun (p, _, _, _) -> pat_has_vector p) cases in
            (* Use multi-discriminant match for tuple scrutinees:
               match l1, l2 with | [], [] => ... instead of
               match (l1, l2) with | ([], []) => ...
               This lets Lean's termination checker see structural recursion.
               Only apply when ALL case arm patterns are P_tup or P_wild. *)
            let pat_is_tup_or_wild (p, _, _, _) = match p.term with
              | P_tup _ | P_wild _ -> true
              | P_paren (_, p', _) -> (match p'.term with P_tup _ | P_wild _ -> true | _ -> false)
              | _ -> false
            in
            (* Extract tuple elements if the scrutinee is a tuple and all patterns
               are tuples/wilds. Yields (arity, elements) for multi-discriminant match. *)
            let tuple_elems = match C.exp_to_term e with
              | Tup (_, es, _) when Seplist.for_all pat_is_tup_or_wild cases ->
                  Some (Seplist.length es, Seplist.to_list es)
              | _ -> None
            in
            let case_line' = match tuple_elems with
              | Some (arity, _) -> case_line_multi inside_instance arity
              | None -> case_line inside_instance
            in
            let body = flat @@ Seplist.to_sep_list_last Seplist.Optional case_line' case_sep cases in
            let match_suffix = if has_vec then from_string ".toList" else emp in
            let match_expr = match tuple_elems with
              | Some (_, elems) ->
                  Output.concat (from_string ", ") (List.map (exp inside_instance) elems)
              | None -> exp inside_instance e
            in
                Output.flat [
                  ws skips; from_string "match "; match_expr; match_suffix; from_string " with "; body; ws skips''
                ]
          | Infix (l, c, r) ->
              let trans e =
                if needs_parens (C.exp_to_term e) then
                  Output.flat [from_string "("; exp inside_instance e; from_string ")"]
                else exp inside_instance e
              in
              let sep = from_string " " in
              begin
                (* This Infix path runs the fail-closed checks (unsupported
                   construct, supply, fuel scope, reader_consumer) but has
                   none of the App path's INJECTION hooks: a reader-lifted
                   constant in infix position emits without its reader
                   arguments, a fuel'd constant without the worker rewrite
                   (its `[LemFuel]` binder is instance-implicit, so it
                   resolves where the scope check passes). Every such case
                   fails VISIBLY at the Lean build (missing binder / unknown
                   worker), never silently. Hook here if a legitimate infix
                   use ever appears. *)
                match C.exp_to_term c with
                  | Constant cd ->
                    begin
                      (* supply net (G-infix leg): a threaded constant in
                         infix position cannot be threaded *)
                      lean_unsupported_check_cref A.env (Typed_ast.exp_to_locn e) cd.descr;
                      supply_net_check (Typed_ast.exp_to_locn e) cd.descr
                        "infix position";
                      fuel_scope_check (Typed_ast.exp_to_locn e) cd.descr "infix position";
                      ireader_scope_check (Typed_ast.exp_to_locn e) cd.descr "infix position";
                      (* reader_consumer in infix position: the leading
                         reader arguments have no sound infix placement *)
                      if is_consumer_cref cd.descr && not !St.rendering_comment then
                        raise (Reporting_basic.err_general true (Typed_ast.exp_to_locn e)
                          "Lean backend: reader_consumer used in infix position (unsupported: the leading reader arguments cannot be injected around an infix operator — use prefix application)");
                      (* In indreln antecedents (Prop context), == and != must use
                         propositional =/≠. This handles the Infix AST case;
                         the App case above handles decomposed forms like not(isEqual x y). *)
                      let c_descr = c_env_lookup Ast.Unknown A.env.c_env cd.descr in
                      match !St.prop_equality, check_beq_target_rep c_descr with
                      | true, Some is_eq ->
                        (* Parenthesize both sides to avoid chained = ambiguity *)
                        let l_out = Output.flat [from_string "("; trans l; from_string ")"] in
                        let r_out = Output.flat [from_string "("; trans r; from_string ")"] in
                        if is_eq then Output.flat [l_out; from_string "  =  "; r_out]
                        else Output.flat [l_out; meta_utf8 "  \xe2\x89\xa0  "; r_out]
                      | _ -> begin
                        (* A symbolic constant rendered by its ASCII name
                           is emitted in PREFIX form, `name l r`: an
                           operand that was fine in infix position (an
                           application `f x`, a nested infix) must now be
                           parenthesised as an argument. *)
                        let trans =
                          if lean_symbolic_name cd.descr <> None then (fun e ->
                            match C.exp_to_term e with
                            | Var _ | Lit _ | Paren _ | Tup _ | List _ | Record _
                            | Begin _ | Constant _ -> exp inside_instance e
                            | _ -> Output.flat [from_string "("; exp inside_instance e; from_string ")"])
                          else trans in
                        let pieces = B.function_application_to_output (exp_to_locn e) trans true e cd [l; r] (use_ascii_rep_for_const cd.descr) in
                        Output.concat sep pieces
                      end
                    end
                  | _           ->
                    begin
                      let mapped = List.map trans [l; c; r] in
                      Output.concat sep mapped
                    end
              end
          | If (skips, test, skips', t, skips'', f) ->
              let render_cond test =
                if needs_parens (C.exp_to_term test) then
                  Output.flat [from_string "("; exp inside_instance test; from_string ")"]
                else exp inside_instance test
              in
              let render_arm (skips, test, skips', t, skips'') =
                Output.flat [
                  ws skips; from_string (lean_if_kw ());
                  from_string " "; render_cond test;
                  ws skips'; from_string "then"; from_string " ";
                  exp inside_instance t;
                  ws skips''; from_string " else "
                ]
              in
              (* Long else-if chains. Lean cannot
                 elaborate an if/else-if chain nested more than ~128 deep
                 ("maximum recursion depth has been reached", independent of
                 the branch contents; measured on 4.28 at 150 and 600 arms);
                 linksem's relocation dispatch has 123-arm chains inside
                 larger terms. A maxRecDepth bump is not a fix. A chain of
                 more than [lean_if_chain_max] arms is emitted in blocks of
                 [lean_if_chain_block]: each later block becomes a local
                 continuation `let _lemIfTailN := fun (_ : Unit) => <block>`
                 (defined innermost-first), and a block's last `else` calls
                 the next one. Pure and order-preserving: the conditions are
                 tested in source order, and a continuation is entered only
                 when every earlier condition was false; `zeta` unfolds it
                 in proofs. *)
              let rec spine e acc =
                match C.exp_to_term e with
                | If (sk, c, sk', t, sk'', f) -> spine f ((sk, c, sk', t, sk'') :: acc)
                | _ -> (List.rev acc, e)
              in
              let (arms, final) = spine f [(skips, test, skips', t, skips'')] in
              if List.length arms <= lean_if_chain_max then
                Output.flat (List.map render_arm arms @ [exp inside_instance final])
              else begin
                (* capture guard: no variable of the chain may use the
                   synthesized prefix *)
                Nfmap.iter (fun n _ ->
                  let ns = Name.to_string n in
                  if lean_starts_with lean_reserved_if_tail_prefix ns then
                    raise (Reporting_basic.err_general true (Typed_ast.exp_to_locn e)
                      (Printf.sprintf "Lean backend: variable '%s' uses the reserved '%s' prefix (synthesized continuations of long if/else-if chains; the reserved-name contract) — rename it" ns lean_reserved_if_tail_prefix)))
                  (C.exp_to_free e);
                let rec split_at k l =
                  if k = 0 then ([], l) else
                  match l with [] -> ([], []) | x :: xs -> let (a, b) = split_at (k - 1) xs in (x :: a, b)
                in
                let rec blocks l =
                  if List.length l <= lean_if_chain_block then [l]
                  else let (a, b) = split_at lean_if_chain_block l in a :: blocks b
                in
                let bs = blocks arms in
                let names = List.map (fun _ ->
                  let n = !St.if_tail_counter in
                  St.if_tail_counter := n + 1;
                  Printf.sprintf "_lemIfTail%d" n) bs in
                let call i = from_string (Printf.sprintf "%s ()" (List.nth names i)) in
                let nb = List.length bs in
                let block_out i b =
                  Output.flat (List.map render_arm b @
                    [if i + 1 < nb then call (i + 1) else exp inside_instance final]) in
                (* continuations for blocks 1..nb-1, innermost (last) first *)
                let lets = List.rev (List.init (nb - 1) (fun j ->
                  let i = j + 1 in
                  Output.flat [from_string "let "; from_string (List.nth names i);
                    from_string " := fun (_ : Unit) => "; block_out i (List.nth bs i);
                    from_string "; "])) in
                Output.flat ([from_string "("] @ lets @ [block_out 0 (List.hd bs); from_string ")"])
              end
          | Quant (quant, quant_binding_list, skips, e) ->
            let quant =
              match quant with
                | Ast.Q_forall _ -> from_string "∀"
                | Ast.Q_exists _ -> from_string "∃"
            in
            let bindings =
              Output.concat (from_string " ") (
                List.map (fun quant_binding ->
                  match quant_binding with
                    | Typed_ast.Qb_var name_lskips_annot ->
                      let name = name_lskips_annot.term in
                      let skip = Name.get_lskip name in
                      let name = Name.strip_lskip name in
                      let name = lean_escape_keyword (Ulib.Text.to_string (Name.to_rope name)) in
                        Output.flat [
                          ws skip; from_string name
                        ]
                    | Typed_ast.Qb_restr (_bool, skips, pat, skips', e, skips'') ->
                      let pat_out = fun_pattern pat in
                        Output.flat [
                          ws skips; pat_out; ws skips'; from_string " : ";
                          exp inside_instance e; ws skips''
                        ]
                ) quant_binding_list)
            in
              Output.flat [
                quant; from_string " "; bindings; from_string ", ("; ws skips;
                exp inside_instance e; from_string " : Prop)"
              ]
          | Comp_binding (_, _, _, _, _, _, _, _, _) ->
              (* Set-comprehension binding — not supported in Lean. Library
                 functions with comprehensions have Lean target reps that
                 bypass this code path (their lem definitions render only as
                 block comments, guarded below); anything LIVE is
                 FAIL-CLOSED: a loud generation-time error. *)
              if !St.rendering_comment then
                from_string "(sorry /- lem: set comprehension binding not supported -/)"
              else
                raise (Reporting_basic.err_general true (exp_to_locn e)
                  "Lean backend: set comprehensions ({ e | bindings ... }) are not supported by the Lean backend; workarounds: rewrite using explicit Set/List library functions (e.g. Set.filter / Set.map / Set.cross, which have Lean target reps), or give the enclosing definition a 'declare lean target_rep'")
          | Setcomp (_, _, _, _, _, _) ->
              if !St.rendering_comment then
                from_string "(sorry /- lem: set comprehension not supported -/)"
              else
                raise (Reporting_basic.err_general true (exp_to_locn e)
                  "Lean backend: set comprehensions ({ e | condition }) are not supported by the Lean backend; workarounds: rewrite using explicit Set/List library functions (e.g. Set.filter / Set.map, which have Lean target reps), or give the enclosing definition a 'declare lean target_rep'")
          | Nvar_e (skips, nvar) ->
            let nvar = id Nexpr_var @@ Ulib.Text.(^^^) (r "") (Nvar.to_rope nvar) in
              Output.flat [
                ws skips; nvar
              ]
          | VectorAcc (e, skips, nexp, skips') ->
              (* Parenthesize match/if/let/fun in function argument position *)
              let e_out =
                if needs_parens (C.exp_to_term e) then
                  Output.flat [from_string "("; exp inside_instance e; from_string ")"]
                else exp inside_instance e
              in
              Output.flat [
                from_string "Vector.get "; e_out;
                from_string " "; src_nexp nexp; ws skips'
              ]
          | VectorSub (e, skips, nexp, skips', nexp', skips'') ->
              let e_out =
                if needs_parens (C.exp_to_term e) then
                  Output.flat [from_string "("; exp inside_instance e; from_string ")"]
                else exp inside_instance e
              in
              Output.flat [
                from_string "Vector.slice "; e_out;
                from_string " "; src_nexp nexp;
                from_string " "; src_nexp nexp'; ws skips''
              ]
          | Vector (skips, es, skips') ->
            let body = flat @@ Seplist.to_sep_list_last (Seplist.Forbid (fun _ -> emp)) (exp inside_instance) (sep @@ from_string ", ") es in
            let skips =
              if skips = Typed_ast.no_lskips then
                from_string " "
              else
                ws skips
            in
              if Seplist.is_empty es then
                Output.flat [
                  skips; from_string "#v[]"
                ]
              else
                Output.flat [
                  skips; from_string "#v["; body; ws skips'; from_string "]"
                ]
    and src_nexp n =
      match n.nterm with
        | Nexp_var (skips, nvar) ->
          let nvar = id Nexpr_var @@ Ulib.Text.(^^^) (r"") (Nvar.to_rope nvar) in
            Output.flat [
              ws skips; nvar
            ]
        | Nexp_const (skips, i) ->
            Output.flat [
              ws skips; from_string (Z.to_string i)
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
    and pat_has_vector (p : pat) : bool =
      match p.term with
        | P_vector _ | P_vectorC _ -> true
        | P_paren (_, p, _) | P_typ (_, p, _, _, _) | P_as (_, p, _, _, _) -> pat_has_vector p
        | P_tup (_, ps, _) | P_list (_, ps, _) -> Seplist.exists pat_has_vector ps
        | P_cons (p1, _, p2) -> pat_has_vector p1 || pat_has_vector p2
        | P_const (_, ps) -> List.exists pat_has_vector ps
        | _ -> false
    and case_line inside_instance (p, skips, e, _) =
        let body =
          if needs_parens (C.exp_to_term e) then
            Output.flat [from_string "("; exp inside_instance e; from_string ")"]
          else exp inside_instance e
        in
        flatten_newlines (Output.flat [
          from_string "| "; def_pattern p; from_string " => "; body
        ])
    (* Multi-discriminant case line: unwrap P_tup pattern into comma-separated
       elements for match l1, l2, ... with | p1, p2, ... => body syntax.
       P_wild is expanded to arity-many wildcards: _ => _, _, ... *)
    and case_line_multi inside_instance arity (p, skips, e, l) =
        let body =
          if needs_parens (C.exp_to_term e) then
            Output.flat [from_string "("; exp inside_instance e; from_string ")"]
          else exp inside_instance e
        in
        let unwrap_tup p = match p.term with
          | P_tup (_, ps, _) ->
            Output.concat (from_string ", ") (List.map def_pattern (Seplist.to_list ps))
          | P_wild _ ->
            Output.concat (from_string ", ") (List.init arity (fun _ -> from_string "_"))
          | _ -> def_pattern p
        in
        let pat_out = match p.term with
          | P_paren (_, p', _) -> unwrap_tup p'
          | _ -> unwrap_tup p
        in
        flatten_newlines (Output.flat [
          from_string "| "; pat_out; from_string " => "; body
        ])
    and field_update inside_instance (fd, skips, e, _) =
      let name = field_ident_to_output fd (use_ascii_rep_for_const fd.descr) in
      (* Flatten newlines in record field values to prevent multiline expressions
         (e.g., lambdas containing match) from breaking record { with } syntax. *)
      let value = flatten_newlines (exp inside_instance e) in
        Output.flat [
          name; ws skips; from_string " := "; value
        ]
    and literal l =
      match l.term with
        | L_true skips -> ws skips ^ from_string "true"
        | L_false skips -> ws skips ^ from_string "false"
        | L_num (skips, n, _) -> ws skips ^ num n
        | L_string (skips, s, _) ->
            let escaped = lean_string_escape s in
            ws skips ^ from_string (String.concat "" ["\""; escaped; "\""])
        | L_unit (skips, skips') -> ws skips ^ from_string "()" ^ ws skips'
        | L_zero s ->
          Output.flat [
            ws s; from_string "false"
          ]
        | L_one s ->
          Output.flat [
            ws s; from_string "true"
          ]
        | L_char (s, c, _) ->
          (* Char.escaped emits decimal escapes — invalid Lean.
             lean_char_escape emits \xHH for non-printable/non-ASCII. *)
          let c = from_string (Printf.sprintf "'%s'" (lean_char_escape c)) in
          Output.flat [
            ws s; c
          ]
        | L_numeral (skips, i, _) ->
          let i = from_string @@ Z.to_string i in
            Output.flat [
              ws skips; i
            ]
        | L_vector (s, prefix, bits) ->
            Output.flat [
              ws s; from_string (String.concat "" [prefix; bits])
            ]
        | L_undefined (skips, explanation) ->
          (* Mirror the OCaml backend,
             which renders L_undefined as a RAISE carrying the
             incomplete-pattern message — `failwith m`
             (src/backend.ml:864, `const_undefined` in module Ocaml at
             src/backend.ml:830) — never a silent default value. The
             Lean rendering is failwithI with the same message, ascribed
             like every other failure site so the Inhabited instance
             resolves at exactly this type; bare-tyvar sites are
             discharged by the threaded [Inhabited tv] binders (the
             pre-pass records L_undefined sites as failure sites,
             renderer-independently: lean_thread_scan_exp). The
             explanation is emitted verbatim between quotes — it is
             pre-escaped with String.escaped at construction
             (src/patterns.ml:1594,1644), exactly as the OCaml backend's
             `str` output relies on. *)
          let typ = l.typ in
          let src_t = C.t_to_src_t typ in
            Output.flat [
              ws skips; from_string "(failwithI \""; from_string explanation;
              from_string "\" : "; pat_typ src_t; from_string ")"
            ]
    and fun_pattern_list inside_instance ps =
      let style = if inside_instance then MatchArm else FunParam in
        Output.flat [
          from_string " "; (concat_str " " @@ List.map (pattern ~style) ps)
        ]
    and src_t_has_wild t =
      match t.term with
        | Typ_wild _ -> true
        | Typ_fn (t1, _, t2) -> src_t_has_wild t1 || src_t_has_wild t2
        | Typ_tup ts -> Seplist.exists src_t_has_wild ts
        | Typ_app (_, ts) -> List.exists src_t_has_wild ts
        | Typ_paren (_, t, _) -> src_t_has_wild t
        | _ -> false
    and pattern ~(style : pat_style) p =
      let self p = pattern ~style p in
      let bare p = pattern ~style:MatchArm p in
      match p.term with
        | P_wild skips ->
          let skips_out =
            if skips = Typed_ast.no_lskips then
              from_string " "
            else
              ws skips
          in
            (match style with
            | FunParam ->
              let t = C.t_to_src_t p.typ in
              Output.flat [from_string "("; skips_out; from_string "_ : "; pat_typ t; from_string ")"]
            | MatchArm ->
              Output.flat [skips_out; from_string "_"])
        | P_var v ->
            (match style with
            | FunParam ->
              let name = lskips_t_to_output v in
              let t = C.t_to_src_t p.typ in
              Output.flat [from_string "("; name; from_string " : "; pat_typ t; from_string ")"]
            | MatchArm ->
              name_var_output v)
        | P_lit l ->
            (match style, l.term with
            | FunParam, L_unit _ -> from_string "(_ : Unit)"
            | _ -> literal l)
        | P_as (skips, p, skips', (n, l), skips'') ->
          let name = name_var_output n in
            Output.flat [
              ws skips; name; from_string "@("; self p; from_string ")"; ws skips''
            ]
        | P_typ (skips, p, skips', t, skips'') ->
            (match style with
            | FunParam ->
              (* When source type has wildcards, use the resolved type from Lem's
                 type checker instead — Lean can't resolve partial wildcards like
                 `rel _ _` with autoImplicit=false *)
              let actual_t = if src_t_has_wild t then C.t_to_src_t p.typ else t in
              Output.flat [
                ws skips; from_string "("; bare p; ws skips'; from_string " :";
                ws skips''; pat_typ actual_t; from_string ")"
              ]
            | MatchArm ->
              Output.flat [
                ws skips; from_string "("; self p; from_string " : "; pat_typ t; from_string ")"; ws skips'
              ])
        | P_tup (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list self (sep @@ from_string ", ") ps in
            (match style with
            | FunParam ->
              Output.flat [ws skips; from_string "("; body; ws skips'; from_string ")"]
            | MatchArm ->
              Output.flat [ws skips; from_string "("; body; from_string ")"; ws skips'])
        | P_record (_, fields, _) ->
            print_and_fail p.locn "illegal record pattern in code extraction, should have been compiled away"
        | P_cons (p1, skips, p2) ->
            (match style with
            | FunParam ->
              Output.flat [
                from_string "("; bare p1; ws skips; from_string " :: "; bare p2; from_string ")"
              ]
            | MatchArm ->
              Output.flat [
                self p1; ws skips; from_string " :: "; self p2
              ])
        | P_var_annot (n, t) ->
            (match style with
            | FunParam ->
              let name = lskips_t_to_output n in
              Output.flat [from_string "("; name; from_string " : "; pat_typ t; from_string ")"]
            | MatchArm ->
              name_var_output n)
        | P_list (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list_last Seplist.Optional self (sep @@ from_string ", ") ps in
            Output.flat [
              ws skips; from_string "["; body; from_string "]"; ws skips'
            ]
        | P_vector (skips, ps, skips') ->
          let body = flat @@ Seplist.to_sep_list_last Seplist.Optional self (sep @@ from_string ", ") ps in
            Output.flat [
              ws skips; from_string "["; body; from_string "]"; ws skips'
            ]
        | P_vectorC _ ->
            raise (Reporting_basic.err_general true p.locn
              "Lean backend: vector concatenation patterns are not supported")
        | P_paren (skips, p, skips') ->
            (match style with
            | FunParam ->
              (* A parenthesised variable `(ev)` in
                 parameter position rendered as `((ev : T))`, which Lean
                 rejects ("expected '_' or identifier"). The shapes below
                 already render as a parenthesised binder `(x : T)`, so the
                 source parentheses add nothing and are dropped (through any
                 nesting: `((z))`). *)
              let rec binder_shaped (q : pat) = match q.term with
                | P_var _ | P_wild _ | P_typ _ | P_var_annot _ -> true
                | P_lit { term = L_unit _ } -> true
                | P_paren (_, q', _) -> binder_shaped q'
                | _ -> false
              in
              if binder_shaped p then Output.flat [ws skips; self p; ws skips']
              else Output.flat [ws skips; from_string "("; self p; ws skips'; from_string ")"]
            | MatchArm ->
              Output.flat [from_string "("; ws skips; self p; ws skips'; from_string ")"])
        | P_const(cd, ps) ->
            let oL = B.pattern_application_to_output p.locn self cd ps (use_ascii_rep_for_const cd.descr) in
            concat (from_string " ") oL
        | P_backend(sk, i, _, ps) ->
            let name = Output.flat [ws sk;
              Ident.to_output (Term_const (false, true)) path_sep (Ident.replace_lskip i Typed_ast.no_lskips)]
            in
            concat (from_string " ") (name :: List.map self ps)
        | P_num_add ((name, l), skips, skips', k) ->
            (* n+k patterns are desugared by is_lean_pattern_match before the
               backend runs. One reaching the renderer is an internal error,
               except inside a definition rendered as a comment (library text
               behind a target representation), where it prints as
               `(name + k)`. *)
            if not !St.rendering_comment then
              raise (Reporting_basic.err_general true p.locn
                "Lean backend: internal error — an n+k pattern reached the Lean renderer (pattern compilation should have removed it)");
            let name = lskips_t_to_output name in
              Output.flat [
                ws skips; from_string "("; name; from_string " + "; from_string (Z.to_string k); from_string ")"
              ]
    and fun_pattern p = pattern ~style:FunParam p
    and def_pattern p = pattern ~style:MatchArm p
    and src_t_has_fn (t : src_t) : bool =
      match t.term with
        | Typ_fn _ -> true
        | Typ_tup ts -> Seplist.exists src_t_has_fn ts
        | Typ_app (id, ts) ->
          (* Check type arguments for functions *)
          List.exists src_t_has_fn ts ||
          (* Also check if the type itself is an abbreviation expanding to a function type.
             This catches cases like stateM 'a 'st = 'st -> maybe ('a * 'st) where the
             abbreviation hides a function type. *)
          (match Types.type_defs_lookup_tc A.env.t_env id.descr with
           | Some (Types.Tc_type td) ->
             (match td.Types.type_abbrev with
               | Some expanded_t ->
                 (* Check if the expanded type contains a function.
                    Use head_norm to fully expand nested abbreviations
                    (e.g., wrap = fn, fn = nat -> bool). *)
                 let rec types_t_has_fn (ty : Types.t) =
                   let ty = Types.head_norm A.env.t_env ty in
                   match ty.Types.t with
                     | Types.Tfn _ -> true
                     | Types.Ttup ts -> List.exists types_t_has_fn ts
                     | Types.Tapp (ts, _) -> List.exists types_t_has_fn ts
                     | _ -> false
                 in
                 types_t_has_fn expanded_t
               | None -> false)
           | _ -> false)
        | Typ_backend (_, ts) -> List.exists src_t_has_fn ts
        | Typ_paren (_, t, _) -> src_t_has_fn t
        | Typ_with_sort (t, _) -> src_t_has_fn t
        | Typ_wild _ | Typ_var _ | Typ_len _ -> false
    (* A variant/record with function-typed fields gets a
       real structural comparison (function fields panic only when reached)
       instead of an always-panicking residual. *)
    and texp_fn_fields (t : texp) : bool =
      match t with
        | Te_variant _ | Te_record _ -> not (texp_can_derive_beq t)
        | Te_opaque | Te_abbrev _ -> false
    and texp_can_derive_beq (t : texp) : bool =
      match t with
        | Te_variant (_, ctors) ->
          not (Seplist.exists (fun (_, _, _, args) ->
            Seplist.exists src_t_has_fn args
          ) ctors)
        | Te_record (_, _, fields, _) ->
          not (Seplist.exists (fun (_, _, _, src_t) -> src_t_has_fn src_t) fields)
        | Te_opaque | Te_abbrev _ -> false
    (* Does Lean's `deriving Ord` order differ
       from OCaml's polymorphic compare on this variant? Lean's derive
       handler ranks constructors by DECLARATION INDEX; OCaml ranks every
       nullary constructor (immediate) below every non-nullary one (block),
       declaration order within each class (runtime/compare.c). The two
       coincide unless a nullary constructor is declared AFTER a block
       constructor. Such variants are routed through the same
       ctor_rank_ocaml-based derivation mutual blocks use, so the OCaml
       rank holds for ALL variants (single and mutual alike). Records
       (field declaration order on both targets) and all-nullary /
       all-block variants keep `deriving`. *)
    and texp_needs_ocaml_rank (t : texp) : bool =
      match t with
        | Te_variant (_, ctors) ->
          let kinds = List.map (fun (_, _, _, args) -> Seplist.to_list args = []) (Seplist.to_list ctors) in
          let rec nullary_after_block seen_block = function
            | [] -> false
            | is_nullary :: rest ->
              (is_nullary && seen_block) || nullary_after_block (seen_block || not is_nullary) rest in
          nullary_after_block false kinds
        | _ -> false
    (* --- Type definition rendering ---
       Dispatch by type form:
       - Te_abbrev → type_def_abbreviation (Lean abbrev)
       - Te_record → type_def_record (Lean structure)
       - Te_variant, single type → type_def_variant (Lean inductive)
       - Te_variant, mutual types with equal params → type_def_variant (mutual block)
       - Te_variant, mutual types with unequal params → type_def_indexed
         (parameters promoted to indices, all types in Type 1 universe)
       After each inductive/structure, constructors are exported and
       BEq/Ord/Inhabited instances are generated. *)
    and type_def_abbreviation n tyvars path skips t =
      let n = B.type_path_to_name n path in
      let name = Name.to_output (Type_ctor (false, false)) n in
      let tyvars' = type_def_type_variables tyvars in
      let tyvar_sep = if List.length tyvars = 0 then emp else from_string " " in
      let body = pat_typ t in
        Output.flat [
          from_string "abbrev"; name; tyvar_sep; tyvars';
          ws skips; from_string " := "; body; from_string "\n";
        ]
    and type_def_record (n', _) tyvars path ty fields =
      let n' = B.type_path_to_name n' path in
      let name = Name.to_output (Type_ctor (false, false)) n' in
      let body = record_fields_with_comments ty fields in
      let tyvars' = type_def_type_variables tyvars in
      let tyvar_sep = if List.length tyvars = 0 then emp else from_string " " in
      let deriving_clause = if texp_can_derive_beq ty then
        from_string "  deriving BEq, Ord\n"
      else emp in
        Output.flat [
          from_string "structure"; name; tyvar_sep; tyvars';
          from_string " where\n"; body; from_string "\n"; deriving_clause;
        ]
    (* Fail-closed checks on every type definition of a block, run before any
       of it is rendered (from def's Type_def arm, so single records — which
       def dispatches to type_def_record directly — are covered too):
       lean_structure_generated_names, lean_check_constructor_width, and a
       type parameter named like a type constructor the definition mentions
       (see lean_tyvar_renames_for: value definitions rename, type
       definitions refuse). *)
    and lean_check_type_block defs =
      List.iter (fun ((n0, l), tnvars, t_path, ty, _) ->
          let tnm = Name.to_string (Name.strip_lskip (B.type_path_to_name n0 t_path)) in
          let body_types = match ty with
            | Te_record (_, _, fields, _) -> List.map (fun (_, _, _, t) -> t) (Seplist.to_list fields)
            | Te_variant (_, ctors) ->
              List.concat_map (fun (_, _, _, args) -> Seplist.to_list args) (Seplist.to_list ctors)
            | Te_abbrev (_, t) -> [t]
            | Te_opaque -> [] in
          let mentioned = List.concat_map (fun t ->
              List.concat_map (lean_type_path_names A.env) (lean_src_t_type_paths t)) body_types in
          List.iter (fun tnv ->
              let tv = tnvar_to_string tnv in
              if List.mem tv mentioned then
                raise (Reporting_basic.err_general true l
                  (Printf.sprintf
                    "Lean backend: type variable '%s of type `%s` is named like a type constructor its definition mentions; the Lean parameter `(%s : Type)` would shadow that type inside the definition — rename the type variable"
                    tv tnm tv)))
            tnvars;
          match ty with
          | Te_record (_, _, fields, _) ->
            let fl = Seplist.to_list fields in
            List.iter (fun ((fname, fl_), f_ref, _, _) ->
                let fnm = Name.to_string (Name.strip_lskip (B.const_ref_to_name fname false f_ref)) in
                if List.mem fnm lean_structure_generated_names then
                  raise (Reporting_basic.err_general true fl_
                    (Printf.sprintf
                      "Lean backend: field `%s` of record type `%s` collides with `%s.%s`, a declaration Lean generates for every structure or inductive type (the constructor `mk` and the auxiliary declarations %s); the name cannot be escaped — rename the field"
                      fnm tnm tnm fnm (String.concat ", " lean_structure_generated_names))))
              fl;
            lean_check_constructor_width l "record type" tnm None (List.length fl)
          | Te_variant (_, ctors) ->
            Seplist.iter (fun ((cn, cl), c_ref, _, args) ->
                let cnm = Name.to_string (Name.strip_lskip (B.const_ref_to_name cn false c_ref)) in
                lean_check_constructor_width cl "variant type" tnm (Some cnm) (Seplist.length args))
              ctors
          | _ -> ())
        (Seplist.to_list defs)
    and type_def inside_module defs =
      St.current_type_block := List.map (fun (_, _, t_path, _, _) -> t_path) (Seplist.to_list defs);
      (* Collect type names and their constructor names for "export" declarations.
         Using "export" instead of "open" ensures constructors are visible
         in files that import this module, not just in the defining file. *)
      let type_info = List.filter_map (fun ((n0, _), _, t_path, ty, _) ->
        match ty with
          | Te_abbrev _ -> None  (* Abbreviations don't create namespaces *)
          | Te_opaque ->
            (* Opaque types with target_rep become abbrevs — no namespace *)
            let l = Ast.Trans (false, "type_info", None) in
            let td = Types.type_defs_lookup l A.env.t_env t_path in
            (match Target.Targetmap.apply_target td.Types.type_target_rep
                    (Target.Target_no_ident Target.Target_lean) with
              | Some (Types.TYR_simple _) -> None
              | _ ->
                let n = B.type_path_to_name n0 t_path in
                Some (Name.to_string (Name.strip_lskip n), []))
          | _ ->
            (* Check if this type has a target_rep — if so, it becomes
               an abbrev and doesn't create a namespace *)
            let l = Ast.Trans (false, "type_info", None) in
            let td = Types.type_defs_lookup l A.env.t_env t_path in
            if Target.Targetmap.apply_target td.Types.type_target_rep
                 (Target.Target_no_ident Target.Target_lean) <> None then None
            else
            let n = B.type_path_to_name n0 t_path in
            let name_str = Name.to_string (Name.strip_lskip n) in
            let ctor_names = match ty with
              | Te_variant (_, ctors) ->
                Seplist.to_list_map (fun ((ctor_n, _), ctor_ref, _, _) ->
                  let cn = B.const_ref_to_name ctor_n false ctor_ref in
                  Name.to_string (Name.strip_lskip cn)
                ) ctors
              | _ -> []
            in
            Some (name_str, ctor_names)
      ) (Seplist.to_list defs) in
      let type_names = List.map fst type_info in
      (* Also register these for the auxiliary file (with namespace qualification) *)
      St.auxiliary_opens := !St.auxiliary_opens @ List.map lean_qualified_name type_names;
      let open_decls = flat (List.map (fun (name_str, ctor_names) ->
        if ctor_names = [] then
          (* Records/opaque types: just open *)
          from_string (String.concat "" ["\nopen "; name_str])
        else
          (* Inductive types: export constructors for cross-file visibility *)
          let ctors_str = String.concat " " ctor_names in
          from_string (String.concat "" ["\nexport "; name_str; " ("; ctors_str; ")"])
      ) type_info) in
      let n = Seplist.length defs in
      if n > 1 then
        (* Separate abbreviations from the mutual block — they are just type aliases
           and can't participate in mutual recursion. Emit them after the mutual block. *)
        let all_defs = Seplist.to_list defs in
        (* The comments before each `and` (in the separator before a type)
           are kept and emitted above that type, wherever it is placed. *)
        let and_comments =
          let (_, pairs) = Seplist.to_pair_list None defs in
          let rec go prev acc = function
            | [] -> acc
            | ((_, _, path, _, _), sk) :: rest -> go sk ((path, prev) :: acc) rest
          in
          go None [] pairs
        in
        let comments_before path =
          match List.assoc_opt path and_comments with
          | None -> emp
          | Some sk -> let (t, l) = split_skip_comments sk in leading_comments ~indent:"" (t @ l)
        in
        let comments_before_sk path =
          match List.assoc_opt path and_comments with None -> None | Some sk -> sk
        in
        (* Partition into abbreviations (with extracted Te_abbrev data) and mutual types.
           Abbreviations can't participate in mutual recursion — they're type aliases.
           Extract Te_abbrev fields during partitioning so downstream code doesn't
           need to re-match on Te_abbrev. *)
        let mutual_defs, abbrev_extracted = List.fold_right (fun (((n0, _), tyvars, path, ty, _) as d) (mut, abbs) ->
          match ty with
          | Te_abbrev (skips, t) -> (mut, (n0, tyvars, path, skips, t) :: abbs)
          | _ -> (d :: mut, abbs)
        ) all_defs ([], []) in
        (* Collect mutual type paths to check if abbreviations reference them *)
        let mutual_paths = List.map (fun ((_, _), _, path, _, _) -> path) mutual_defs in
        (* Split abbreviations: those referencing mutual types go after,
           others go before (they may be needed by the mutual types). *)
        let abbrevs_before, abbrevs_after = List.partition
          (fun (_, _, _, _, t) -> not (src_t_references_paths mutual_paths t))
          abbrev_extracted in
        let render_abbrev (n0, tyvars, path, skips, t) =
          let n = B.type_path_to_name n0 path in
          let name = Name.to_output (Type_ctor (false, false)) n in
          let tyvars' = type_def_type_variables tyvars in
          let tyvar_sep = if List.length tyvars = 0 then emp else from_string " " in
          Output.flat [
            from_string "\n"; comments_before path; from_string "abbrev"; name; tyvar_sep; tyvars';
            ws skips; from_string " := "; pat_typ t
          ]
        in
        let abbrevs_before_output = flat @@ List.map render_abbrev abbrevs_before in
        let abbrevs_after_output = flat @@ List.map render_abbrev abbrevs_after in
        let mutual_n = List.length mutual_defs in
        (* Note: mutual record names are pre-collected in lean_defs before the
           main fold_right, so we don't register them here. See St.mutual_records
           pre-collection near St.local_modules. *)
        let mutual_output =
          if mutual_n > 1 then
            let rec with_next_comments = function
              | [] -> []
              | [d] -> [(d, None)]
              | d :: ((_, _, next_path, _, _) :: _ as rest) ->
                (d, comments_before_sk next_path) :: with_next_comments rest
            in
            let mutual_sep = Seplist.from_list (with_next_comments mutual_defs) in
            let and_sep sk =
              let (t, l) = split_skip_comments sk in
              Output.flat [from_string "\n"; leading_comments ~indent:"" (t @ l); from_string "inductive"]
            in
            (* Check if all types in mutual block have the same number of type params *)
            let param_counts = List.map (fun (_, ty_vars, _, _, _) ->
              List.length ty_vars
            ) mutual_defs in
            let all_same = match param_counts with
              | [] -> true
              | x :: xs -> List.for_all (fun y -> y = x) xs
            in
            if all_same then
              (* A record in a mutual block is a `structure` (Lean accepts
                 structures, recursive through List/Option, in a mutual
                 block with inductives); the other members are inductives. *)
              let member ((((n0, _), ty_vars, t_path, ty, _)) as d) =
                match ty with
                | Te_record (_, _, fields, _) ->
                  let n = B.type_path_to_name n0 t_path in
                  Output.flat [ from_string "structure"; inductive (List.map tnvar_to_variable ty_vars) n;
                                from_string " where\n"; record_fields_with_comments ty fields ]
                | _ -> Output.flat [ from_string "inductive"; type_def_variant false d ]
              in
              let member_sep sk =
                let (t, l) = split_skip_comments sk in
                Output.flat [from_string "\n"; leading_comments ~indent:"" (t @ l)]
              in
              let body = flat @@ Seplist.to_sep_list member member_sep mutual_sep in
              Output.flat [ from_string "mutual\n"; body; from_string "\nend" ]
            else
              let body = flat @@ Seplist.to_sep_list type_def_indexed and_sep mutual_sep in
              Output.flat [ from_string "mutual\ninductive"; body; from_string "\nend" ]
          else if mutual_n = 1 then
            let single_sep = Seplist.from_list_default None mutual_defs in
            let body = flat @@ Seplist.to_sep_list (type_def_variant true) (sep @@ from_string "\n") single_sep in
            Output.flat [ from_string "inductive"; body ]
          else
            emp  (* All were abbreviations *)
        in
        (* Accessor functions for the records that are still single-constructor
           inductives (those in a block whose members have different numbers
           of type parameters, see mutual_block_records_as_inductives): an
           inductive has no field projections, so dot notation needs these
           defs. A record emitted as a structure has Lean's projections, under
           the same names. *)
        let accessor_defs = flat @@ List.filter_map (fun ((n0, _), ty_vars_raw, path, ty, _) ->
          match ty with
            | Te_record (_, _, fields, _) when lean_record_is_inductive path ->
              let n = B.type_path_to_name n0 path in
              let type_name = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip n)) in
              let tv_decl = String.concat "" @@ List.map (fun tv ->
                let s = tnvar_to_string tv in
                match tv with
                  | Typed_ast.Tn_A _ -> String.concat "" [" {"; s; " : Type}"]
                  | Typed_ast.Tn_N _ -> String.concat "" [" {"; s; " : Nat}"]
              ) ty_vars_raw in
              let tv_applied = String.concat " " @@ List.map tnvar_to_string ty_vars_raw in
              let tv_sep = if List.length ty_vars_raw = 0 then "" else " " in
              let field_list = Seplist.to_list fields in
              let n_fields = List.length field_list in
              let accessors = List.mapi (fun i ((fname, _), f_ref, _, src_t) ->
                let field_name = B.const_ref_to_name fname false f_ref in
                let field_str = lean_escape_keyword (Ulib.Text.to_string (Name.to_rope (Name.strip_lskip field_name))) in
                let pre_wildcards = String.concat "" (List.init i (fun _ -> " _")) in
                let post = if i < n_fields - 1 then " .." else "" in
                Output.flat [
                  from_string (String.concat "" [
                    "\n@[inline] def "; type_name; "."; field_str;
                    tv_decl;
                    " (self : "; type_name; tv_sep; tv_applied;
                    ") : "
                  ]);
                  pat_typ src_t;
                  from_string (String.concat "" [
                    " :=\n  match self with | .mk";
                    pre_wildcards; " "; field_str; post; " => "; field_str
                  ])
                ]
              ) field_list in
              Some (flat accessors)
            | _ -> None
        ) mutual_defs in
        (* Abbreviations that don't reference mutual types go BEFORE (they may be
           needed by the mutual types). Abbreviations that DO reference mutual types
           go AFTER (they alias types defined in the block). *)
        let before_sep = if abbrevs_before = [] then emp else from_string "\n" in
        Output.flat [ abbrevs_before_output; before_sep; mutual_output; abbrevs_after_output; open_decls; accessor_defs; from_string "\n" ]
      else
        (* Check if this type has a Lean target_rep type (TYR_simple).
           If so, emit abbrev instead of inductive — the type is defined
           in external Lean code. Works for both opaque types and types
           with constructors that have their own target_reps. *)
        let ((n0, _), tyvars, t_path, ty, _) = Seplist.hd defs in
        let target_rep_abbrev =
            let l = Ast.Trans (false, "type_def", None) in
            let td = Types.type_defs_lookup l A.env.t_env t_path in
            begin match Target.Targetmap.apply_target td.Types.type_target_rep
                    (Target.Target_no_ident Target.Target_lean) with
              | Some (Types.TYR_simple (_, _, target_ident)) ->
                (* Collect import for the type target rep's module *)
                let target_id_str = Ident.to_string target_ident in
                collect_cr_simple_import false target_id_str;
                let name = B.type_path_to_name n0 t_path in
                let name_out = Name.to_output (Type_ctor (false, false)) name in
                let tyvars_out = type_def_type_variables tyvars in
                let tyvar_sep = if List.length tyvars = 0 then emp else from_string " " in
                Some (Output.flat [
                  from_string "abbrev "; name_out; tyvar_sep; tyvars_out;
                  from_string " := ";
                  Ident.to_output (Type_ctor (false, true)) (r".") target_ident;
                  from_string "\n"
                ])
              | _ -> None
            end
        in
        match target_rep_abbrev with
          | Some abbrev_out -> abbrev_out
          | None ->
            let body = flat @@ Seplist.to_sep_list (type_def_variant true) (sep @@ from_string "\n") defs in
            Output.flat [ from_string "inductive"; body; open_decls; from_string "\n" ]
    and type_def_variant emit_deriving ((n0, l), ty_vars, t_path, ty, _) =
      let n = B.type_path_to_name n0 t_path in
      let name = Name.to_output (Type_ctor (false, false)) n in
      let ty_vars =
        List.map tnvar_to_variable ty_vars
      in
        match ty with
          | Te_opaque ->
              Output.flat [
                inductive ty_vars n; from_string " : Type where"
              ]
          | _ ->
            Output.flat [
              inductive ty_vars n; from_string " : Type"; tyexp emit_deriving name ty_vars ty
            ]
    and type_def_indexed ((n0, l), ty_vars, t_path, ty, _) =
      (* Emit type with indices instead of parameters, for heterogeneous mutual blocks.
         Parameters become indices: inductive v : (a : Type) → (b : Type) → Type 1 where *)
      let n = B.type_path_to_name n0 t_path in
      let name = Name.to_output (Type_ctor (false, false)) n in
      let ty_vars_list =
        List.map tnvar_to_variable ty_vars
      in
      let indices =
        if List.length ty_vars_list = 0 then emp
        else
          let mapped = List.map (fun v ->
            match v with
              | Tyvar x -> Output.flat [ from_string "("; x; from_string " : Type) → " ]
              | Nvar x -> Output.flat [ from_string "("; x; from_string " : Nat) → " ]
          ) ty_vars_list in
          concat emp mapped
      in
      (* All types in a heterogeneous mutual block must live in the same universe.
         Since at least one type has indices (parameters promoted to indices),
         that type lives in Type 1, so ALL types must be Type 1. *)
      let universe = from_string "Type 1" in
      let ty_vars_names =
        concat_str " " @@ List.map (fun v ->
          match v with
            | Tyvar out -> out
            | Nvar out -> out
        ) ty_vars_list
      in
      let ty_vars_names_space = if List.length ty_vars_list = 0 then emp else from_string " " in
      match ty with
        | Te_variant (skips, ctors) ->
          let body = flat @@ Seplist.to_sep_list_first Seplist.Optional
            (constructor_indexed name ty_vars_list ty_vars_names ty_vars_names_space) (sep @@ from_string "\n") ctors in
          Output.flat [
            from_string " "; name; from_string " : "; indices; universe; from_string " where";
            ws skips; from_string "\n"; body
          ]
        | Te_opaque ->
          Output.flat [
            from_string " "; name; from_string " : "; indices; universe; from_string " where"
          ]
        | Te_record (_, _, fields, _) ->
          (* Records in heterogeneous mutual blocks: emit as single-constructor
             indexed inductive with named fields.  Use the same (fname : type) →
             syntax as tyexp's Te_record case but prefix implicit type bindings
             (like constructor_indexed) since parameters are promoted to indices. *)
          let field_list = Seplist.to_list fields in
          let mk_args = flat @@ List.map (fun ((n, _), f_ref, _skips, t) ->
            Output.flat [
              from_string "(";
              field_decl_output n f_ref;
              from_string " :"; pat_typ t;
              from_string ") → "
            ]
          ) field_list in
          let implicit_bindings =
            if List.length ty_vars_list = 0 then emp
            else
              let mapped = List.map (fun v ->
                match v with
                  | Tyvar x -> Output.flat [ from_string "{"; x; from_string " : Type} → " ]
                  | Nvar x -> Output.flat [ from_string "{"; x; from_string " : Nat} → " ]
              ) ty_vars_list in
              concat emp mapped
          in
          Output.flat [
            from_string " "; name; from_string " : "; indices; universe; from_string " where\n";
            from_string "  | mk : "; implicit_bindings; mk_args;
            name; ty_vars_names_space; ty_vars_names
          ]
        | Te_abbrev _ ->
          (* Abbreviations are dispatched before this point (type_def);
             reaching here is an internal error, as in tyexp. *)
          raise (Reporting_basic.err_general true l
            "Lean backend: internal error — an abbreviation reached type_def_indexed")
    and constructor_indexed ind_name (ty_vars : variable list) ty_vars_names ty_vars_names_space ((name0, _), c_ref, skips, args) =
      let ctor_name = B.const_ref_to_name name0 false c_ref in
      let ctor_name = Name.to_output (Type_ctor (false, false)) ctor_name in
      let body = flat @@ Seplist.to_sep_list ctor_arg_typ (sep @@ from_string " → ") args in
      (* For indexed inductives, constructors must bind all type variables implicitly *)
      let implicit_bindings =
        if List.length ty_vars = 0 then emp
        else
          let mapped = List.map (fun v ->
            match v with
              | Tyvar x -> Output.flat [ from_string "{"; x; from_string " : Type} → " ]
              | Nvar x -> Output.flat [ from_string "{"; x; from_string " : Nat} → " ]
          ) ty_vars in
          concat emp mapped
      in
      let tail =
        Output.flat [
          from_string " → "; ind_name; ty_vars_names_space; ty_vars_names
        ]
      in
        if Seplist.length args = 0 then
          Output.flat [
            from_string "  | "; ctor_name; from_string " :"; ws skips; implicit_bindings; ind_name
          ; ty_vars_names_space; ty_vars_names
          ]
        else
          Output.flat [
            from_string "  | "; ctor_name; from_string " :"; ws skips; implicit_bindings; body; tail
          ]
    and inductive ty_vars name =
      let ty_var_sep = if List.length ty_vars = 0 then emp else from_string " " in
      let ty_vars = inductive_type_variables ty_vars in
      let name = Name.to_output (Type_ctor (false, false)) name in
        Output.flat [
          from_string " "; name; ty_var_sep; ty_vars
        ]
    and inductive_type_variables vars =
      let mapped = List.map (fun v ->
          match v with
            | Tyvar x ->
              Output.flat [
                from_string "("; x; from_string " : Type)"
              ]
            | Nvar x ->
              Output.flat [
                from_string "("; x; from_string " : Nat)"
              ]) vars
      in
        concat_str " " mapped
    and tyexp emit_deriving name ty_vars ty =
      match ty with
        | Te_opaque ->
            (* Unreachable: type_def_variant handles Te_opaque directly *)
            raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected Te_opaque in tyexp")
        | Te_abbrev _ ->
            (* Unreachable: def dispatches abbreviations to type_def_abbreviation *)
            raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: unexpected Te_abbrev in tyexp")
        | Te_record (_, _, fields, _) ->
            (* Records in mutual blocks: emit as single-constructor inductive
               (Lean 4 mutual blocks cannot contain structure definitions) *)
            let field_list = Seplist.to_list fields in
            let mk_args = flat @@ List.map (fun ((n, _), f_ref, _skips, t) ->
              Output.flat [
                from_string " (";
                field_decl_output n f_ref;
                from_string " :"; ctor_arg_typ t;
                from_string ")"
              ]
            ) field_list in
            (* Build return type with applied type variables: e.g. "statement a" *)
            let ty_vars_applied =
              concat_str " " @@ List.map (fun v ->
                match v with
                  | Tyvar out -> out
                  | Nvar out -> out
              ) ty_vars
            in
            let ty_vars_sep = if List.length ty_vars = 0 then emp else from_string " " in
            Output.flat [
              from_string " where\n  | mk"; mk_args; from_string " : "; name; ty_vars_sep; ty_vars_applied
            ]
        | Te_variant (skips, ctors) ->
          (* One constructor per line. The source layout before each `|` is
             replaced; its comments are kept (trailing ones on the previous
             constructor's line, leading ones on their own lines). *)
          let ctor_sep sk =
            let (t, l) = split_skip_comments sk in
            Output.flat [trailing_comments t; from_string "\n"; leading_comments ~indent:"  " l]
          in
          let first_sep sk =
            let (t, l) = split_skip_comments sk in
            leading_comments ~indent:"  " (t @ l)
          in
          let body = flat @@ Seplist.to_sep_list_first (Seplist.Forbid first_sep)
                       (constructor name ty_vars) ctor_sep ctors in
          let is_all_nullary = Seplist.for_all (fun (_, _, _, args) -> Seplist.to_list args = []) ctors in
          let deriving_clause = if (emit_deriving || is_all_nullary) && texp_can_derive_beq ty
                                   && not (texp_needs_ocaml_rank ty) then
            from_string "\n  deriving BEq, Ord"
          else emp in
            let (where_t, where_l) = split_skip_comments skips in
            Output.flat [
              from_string " where"; trailing_comments where_t; from_string "\n";
              leading_comments ~indent:"  " where_l; body; deriving_clause
            ]
    and constructor ind_name (ty_vars : variable list) ((name0, _), c_ref, skips, args) =
      let ctor_name = B.const_ref_to_name name0 false c_ref in
      let ctor_name = Name.to_output (Type_ctor (false, false)) ctor_name in
      let body = flat @@ Seplist.to_sep_list ctor_arg_typ (sep @@ from_string " → ") args in
      let ty_vars_typeset =
        concat_str " " @@ List.map (fun v ->
          match v with
            | Tyvar out -> out
            | Nvar out -> out
        ) ty_vars
      in
      let tail =
        Output.flat [
          from_string " → "; ind_name; from_string " "; ty_vars_typeset
        ]
      in
        if Seplist.length args = 0 then
          Output.flat [
            from_string "  | "; ctor_name; from_string " :"; ws skips; ind_name
          ; from_string " "; ty_vars_typeset
          ]
        else
          Output.flat [
            from_string "  | "; ctor_name; from_string " :"; ws skips; body; tail
          ]
    (* Constructor argument types and nested inductives. Lean's kernel
       accepts a nested occurrence `List (X ty)` only when
       X is an inductive type applied to arguments; a Lem type ABBREVIATION
       emitted as a Lean `abbrev` is not unfolded there, so
       `abbrev dim t := Option Nat × Option t`, `| arr : List (dim t) → top t`
       and later `inductive ty | CT : top ty → ty` fails with "(kernel) arg
       #1 of '_nested.List_2.cons' contains a non valid occurrence of the
       datatypes being declared" (linksem's dwarf.lem c_type_top/c_type).
       In an inductive constructor argument, an abbreviation (without a Lean
       target rep) whose expansion mentions a type parameter or a type of the
       group being defined is therefore printed EXPANDED. Closed
       abbreviations keep their names, so nothing else changes. *)
    and ctor_arg_typ (t : src_t) =
      let changed = ref false in
      let rec mentions_block (ty : Types.t) =
        match ty.Types.t with
        | Types.Tapp (ts, p) ->
          List.exists (fun q -> Path.compare p q = 0) !St.current_type_block
          || List.exists mentions_block ts
        | Types.Tfn (a, b) -> mentions_block a || mentions_block b
        | Types.Ttup ts -> List.exists mentions_block ts
        | _ -> false
      in
      let rec expand (ty : Types.t) : Types.t =
        match ty.Types.t with
        | Types.Tapp (ts, p) ->
          (match Types.type_defs_lookup_tc A.env.t_env p with
           | Some (Types.Tc_type td)
             when td.Types.type_abbrev <> None
               && Target.Targetmap.apply_target td.Types.type_target_rep
                    (Target.Target_no_ident Target.Target_lean) = None ->
             let body = match td.Types.type_abbrev with Some b -> b | None -> assert false in
             let body = Types.type_subst (Types.TNfmap.from_list2 td.Types.type_tparams ts) body in
             if not (Types.TNset.is_empty (Types.free_vars body)) || mentions_block body then begin
               changed := true; expand body
             end else { Types.t = Types.Tapp (List.map expand ts, p) }
           | _ -> { Types.t = Types.Tapp (List.map expand ts, p) })
        | Types.Tfn (a, b) -> { Types.t = Types.Tfn (expand a, expand b) }
        | Types.Ttup ts -> { Types.t = Types.Ttup (List.map expand ts) }
        | _ -> ty
      in
      let e = expand t.typ in
      if !changed then Output.flat [ws (snd (Types.typ_alter_init_lskips (fun sk -> (sk, sk)) t)); from_string "("; pat_typ (C.t_to_src_t e); from_string ")"]
      else pat_typ t
    and pat_typ t =
      match t.term with
        | Typ_wild skips -> ws skips ^ from_string "_"
        | Typ_var (skips, v) ->
            Output.flat [
              ws skips; id Type_var (r (lean_tyvar_text (Ulib.Text.to_string (Tyvar.to_rope v))))
            ]
        | Typ_fn (t1, skips, t2) ->
            if skips = Typed_ast.no_lskips then
              pat_typ t1 ^ from_string " → " ^ ws skips ^ pat_typ t2
            else
              pat_typ t1 ^ from_string " →" ^ ws skips ^ pat_typ t2
        | Typ_tup ts ->
            let body = flat @@ Seplist.to_sep_list pat_typ (sep @@ from_string " ×") ts in
              from_string "(" ^ body ^ from_string ")"
        | Typ_app (p, ts) ->
            lean_unsupported_check_type A.env t.locn p.descr;
            if Path.compare p.descr Path.unitpath = 0 then
              let sk = Typed_ast.ident_get_lskip p in
              Output.flat [ ws sk; from_string "Unit" ]
            else
            let (ts_list, head) = B.type_app_to_output pat_typ p ts in
            let ts_out = concat_str " " @@ List.map pat_typ ts_list in
            let space = if ts_list = [] then emp else from_string " " in
              Output.flat [
                head; space; ts_out
              ]
        | Typ_paren(skips, t, skips') ->
            (* Parentheses around an atom (`Option (Nat)`) or around a type
               that brings its own (a tuple, a doubled paren) are redundant;
               Lem's type conversion adds them generically. Atomicity is
               decided on the printed text: a type with a target
               representation can print as several tokens. Comments keep
               the parentheses. *)
            let inner = pat_typ t in
            let has_comments =
              List.exists (fun sk -> split_skip_comments sk <> ([], []))
                (skips :: skips' :: src_t_skips t) in
            (* an atom: a (possibly qualified) name, no spaces or brackets *)
            let text = String.trim (lean_output_str inner) in
            let atomic =
              text <> ""
              && String.for_all (fun c ->
                  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
                  || c = '_' || c = '.' || c = '\'' || Char.code c >= 128) text
            in
            let self_parenthesised = match t.term with Typ_tup _ | Typ_paren _ -> true | _ -> false in
            if not has_comments && (atomic || self_parenthesised) then ws skips ^ inner
            else ws skips ^ from_string "(" ^ inner ^ ws skips' ^ from_string ")"
        | Typ_with_sort(t,_) -> raise (Reporting_basic.err_general true t.locn "Lean backend: target sort annotations are not supported")
        | Typ_len nexp -> src_nexp nexp
        | Typ_backend (p, ts) ->
          let i = Path.to_ident (ident_get_lskip p) p.descr in
          if String.trim (Ident.to_string i) = "sorry" then
            raise (lean_sorry_rep_error t.locn "inline backend type");
          let i = Ident.to_output (Type_ctor (false, true)) path_sep i in
          let ts_out = List.map pat_typ ts in
          let space = if ts_out = [] then emp else from_string " " in
            Output.flat [
              i; space; concat_str " " ts_out
            ]
    and type_def_type_variables tvs =
      match tvs with
        | [] -> emp
        | [Typed_ast.Tn_A tv] -> from_string "(" ^ tyvar tv ^ from_string " : Type)"
        | tvs ->
          let mapped = List.map (fun t ->
            let name = tnvar_to_string t in
            Output.flat [from_string "("; from_string name; from_string " : "; from_string (tnvar_kind t); from_string ")"]
          ) tvs
          in
            Output.flat [
              from_string " "; concat_str " " mapped
            ]
    and indreln_typ t =
      match t.term with
        | Typ_wild skips -> ws skips ^ from_string "_"
        | Typ_var (skips, v) -> ws skips ^ (id Type_var (r (lean_tyvar_text (Ulib.Text.to_string (Tyvar.to_rope v)))))
        | Typ_fn (t1, skips, t2) ->
          begin
            match t2.term with
              | Typ_app (p, []) ->
                if p.descr = Path.boolpath then
                  indreln_typ t1 ^ ws skips ^ from_string " → " ^ from_string "Prop"
                else
                  indreln_typ t1 ^ ws skips ^ from_string " → " ^ indreln_typ t2
              | _ ->
                indreln_typ t1 ^ ws skips ^ from_string " → " ^ indreln_typ t2
          end
        | Typ_tup ts ->
            let body = flat @@ Seplist.to_sep_list indreln_typ (sep @@ from_string " ×") ts in
              from_string "(" ^ body ^ from_string ")"
        | Typ_app (p, ts) ->
          (* Use type_app_to_output to handle target reps (e.g. set → List) *)
          let (remaining_ts, name_output) = B.type_app_to_output indreln_typ p ts in
          let args = concat_str " " @@ List.map indreln_typ remaining_ts in
          let args_space = if remaining_ts <> [] then from_string " " else emp in
            Output.flat [
              name_output; args_space; args
            ]
        | Typ_paren(skips, t, skips') ->
            ws skips ^ from_string "(" ^ indreln_typ t ^ from_string ")" ^ ws skips'
        | Typ_with_sort(t, _) -> indreln_typ t
        | Typ_len nexp -> src_nexp nexp
        | Typ_backend (p, ts) ->
          let i = Path.to_ident (ident_get_lskip p) p.descr in
          if String.trim (Ident.to_string i) = "sorry" then
            raise (lean_sorry_rep_error t.locn "inline relation backend type");
          let i = Ident.to_output (Type_ctor (false, true)) path_sep i in
          let ts_out = List.map indreln_typ ts in
          let space = if ts_out = [] then emp else from_string " " in
            Output.flat [
              i; space; concat_str " " ts_out
            ]
    (* The fields of a record, one per line, with the author's comments:
       the comments at the opening `<|` above the first field; a field's
       leading comments (in its name's skips, after a line break)
       on their own lines above it; comments after its type (before the `;`,
       or after the `;` on the same line) at the end of its line; comments
       before the closing `|>` after the last field. *)
    and record_fields_with_comments ty fields =
      let rskips = match ty with Te_record (_, _, _, sk) -> sk | _ -> None in
      (* the comments before and at the opening `<|` lead the first field *)
      let open_comments = match ty with
        | Te_record (s1, s2, _, _) ->
          List.concat_map (fun sk -> let (t, l) = split_skip_comments sk in t @ l) [s1; s2]
        | _ -> [] in
      let (_, pairs) = Seplist.to_pair_list None fields in
      let items = Array.of_list (List.map fst pairs) in
      let seps = Array.of_list (List.map snd pairs) in
      let k = Array.length items in
      let trail = Array.make (k + 1) [] and lead = Array.make (k + 1) [] in
      lead.(0) <- open_comments;
      Array.iteri (fun i ((n, _), _, _, _) ->
          let (t, l) = split_skip_comments (Name.get_lskip n) in
          if i > 0 then trail.(i - 1) <- trail.(i - 1) @ t else lead.(0) <- lead.(0) @ t;
          lead.(i) <- lead.(i) @ l)
        items;
      Array.iteri (fun i sk ->
          let (t, l) = split_skip_comments sk in
          trail.(i) <- trail.(i) @ t;
          lead.(i + 1) <- lead.(i + 1) @ l)
        seps;
      let (rt, rl) = split_skip_comments rskips in
      if k > 0 then trail.(k - 1) <- trail.(k - 1) @ rt else lead.(k) <- rt;
      lead.(k) <- lead.(k) @ rl;
      let lines = List.mapi (fun i f ->
          Output.flat [leading_comments ~indent:"  " lead.(i); field f; trailing_comments trail.(i)])
          (Array.to_list items) in
      Output.flat [concat_str "\n" lines;
                   (if lead.(k) = [] then emp
                    else Output.flat [from_string "\n"; leading_comments ~indent:"  " lead.(k)])]
    and field ((n, _), f_ref, _skips, t) =
      Output.flat [
          from_string "  ";
          field_decl_output n f_ref;
          from_string " :"; pat_typ t
      ]
    (* --- Instance generation ---
       For each type definition, generates:
       1. Inhabited instance(s): tier 1 (safe constructor) or tier-2
          per-constructor bounded derivation (fail-closed —
          underivable types get no instance and backend-visible demands
          on them are generation-time errors)
       2. BEq + Ord (via `deriving` if possible; otherwise derived
          structural comparisons or loud failwithI residuals; Type-1
          blocks are a generation-time error, fail-closed like the
          Inhabited path)
       3. SetType / Eq0 / Ord0 instances (with [BEq]/[Ord] constraints for parameterized types)
       Mutual types use find_safe_ctor_for_mutual to avoid self-referential defaults.
       Library opaque types (phantom types like ty1..ty4096) skip instance generation. *)
    (* src_t_references_paths / src_t_is_directly_mutual /
       find_safe_ctor_for_mutual / the derivability analysis now live at
       top level (shared with lean_inhabited_prepass). *)
    (* Fail-closed demand check (design note rule 5): the backend is
       about to emit a value-level
       `default` — an Inhabited demand it KNOWS about, inside a generated
       instance body — at an applied type. If the census says derivation
       FAILED for that type (Inh_none), refuse at generation time, naming
       the type and both escape hatches. *)
    and inhabited_demand_check (p : Path.t) : unit =
      if inhabited_census_debug then
        Printf.eprintf "DEMAND check %s -> %s\n%!" (Path.to_string p)
          (match inhabited_census_lookup p with None -> "absent" | Some (_, Inh_none) -> "NONE" | Some (_, Inh_instances _) -> "inst");
      match inhabited_census_lookup p with
        | Some (n, Inh_none) ->
          raise (Reporting_basic.err_general true Ast.Unknown (Printf.sprintf
            "Lean backend: cannot derive an Inhabited instance for type '%s' (no constructor with derivably-inhabitable fields), but generated code demands one; escape hatches: 'declare {lean} skip_instances type %s' plus a hand-written Lean instance, or 'declare lean target_rep type %s' mapping it to a hand-written Lean type" n n n))
        | _ -> ()
    (* Render the [Inhabited tv] binders for the bound tyvars, in the
       type's parameter declaration order. *)
    and inhabited_bound_binders tnvar_list (bounds : string list) : Output.t =
      Output.flat (List.filter_map (fun tv ->
        let n = tnvar_to_string tv in
        if List.mem n bounds then
          Some (Output.flat [from_string " [Inhabited "; from_string n; from_string "]"])
        else None) tnvar_list)
    (* Default value for a source type in Inhabited context.
       mutual_name_map: when non-empty, direct references to mutual types use
       TypeName.default_inhabited instead of default (for mutual def blocks
       where Inhabited instances don't exist yet). *)
    and default_value_inhabited ?(mutual_name_map=[]) (s : src_t) : Output.t =
      let recurse = default_value_inhabited ~mutual_name_map in
      match s.term with
        | Typ_app (id, _) when mutual_name_map <> [] ->
          (match List.assoc_opt id.descr mutual_name_map with
            | Some type_name_str -> from_string (String.concat "" [type_name_str; ".default_inhabited"])
            | None -> (inhabited_demand_check id.descr; from_string "default"))
        | Typ_app (id, _) -> inhabited_demand_check id.descr; from_string "default"
        | Typ_wild _ | Typ_var _ | Typ_backend _ -> from_string "default"
        | Typ_len _ -> from_string "0"
        | Typ_tup seplist ->
            let mapped = List.map recurse (Seplist.to_list seplist) in
            Output.flat [from_string "("; concat_str ", " mapped; from_string ")"]
        | Typ_paren (_, src_t, _)
        | Typ_with_sort (src_t, _) -> recurse src_t
        | Typ_fn (dom, _, rng) ->
            let v = generate_fresh_name () in
            Output.flat [
              from_string "(fun ("; from_string v; from_string " : "; pat_typ dom;
              from_string ") => "; recurse rng; from_string ")"
            ]
    and generate_default_value_texp (t: texp) =
      match t with
        | Te_opaque ->
          (* Opaque types are tier-2/fail-closed — they never reach the
             tier-1 default renderer. *)
          raise (Reporting_basic.err_general true Ast.Unknown
            "Lean backend: internal error — Te_opaque in generate_default_value_texp is unreachable (opaque types are fail-closed)")
        | Te_abbrev (_, src_t) -> default_value_inhabited src_t
        | Te_record (_, _, seplist, _) ->
            let fields = Seplist.to_list seplist in
            let mapped = List.map (fun ((name, _), const_descr_ref, _, src_t) ->
              let name = B.const_ref_to_name name true const_descr_ref in
              let o = lskips_t_to_output name in
              let s = default_value_inhabited src_t in
              Output.flat [o; from_string " := "; s]
            ) fields in
            Output.flat [from_string "{ "; concat_str ", " mapped; from_string " }"]
        | Te_variant _ ->
            raise (Reporting_basic.err_general true Ast.Unknown "Lean backend: Te_variant in generate_default_value_texp is unreachable")
    (* Render a constructor call for an Inhabited default value *)
    and render_ctor_default ?(mutual_name_map=[]) ((ctor_name, _), ctor_ref, _, src_ts) =
      let n = B.const_ref_to_name ctor_name false ctor_ref in
      let ys = Seplist.to_list src_ts in
      let mapped = List.map (default_value_inhabited ~mutual_name_map) ys in
      let sep = if List.length mapped = 0 then emp else from_string " " in
      Output.flat [lskips_t_to_output n; sep; concat_str " " mapped]
    (* Compute whether to skip Inhabited for this type (abbreviations, types with
       target_rep, or types annotated with 'declare {lean} skip instances') *)
    and skip_inhabited_for_type t path =
      skip_inhabited_for_type_env A.env t path
    (* Compute the default value expression for a TIER-1 Inhabited instance.
       mutual_name_map: (Path.t * string) list mapping mutual type paths to their
       Lean names. When non-empty, uses TypeName.default_inhabited for mutual type
       args (for use inside mutual def blocks where Inhabited instances don't exist yet). *)
    (* Returns None when tier 1 has no safe constructor: the caller must
       then render the pre-pass tier-2 plan (per-constructor bounded
       instances). The tier
       split itself is inhabited_needs_tier2 (top level, shared with the
       pre-pass so the plan and the emission can never disagree). *)
    and inhabited_default_expr ?(mutual_name_map=[]) mutual_paths (((name, _), tnvar_list, path, t, _) as td) : Output.t option =
      if inhabited_needs_tier2 mutual_paths td then None
      else if tnvar_list = [] then
        Some (match t with
          | Te_variant (_, seplist) ->
            let ctors = Seplist.to_list seplist in
            (match find_safe_ctor_for_mutual mutual_paths ctors with
              | Some ctor -> render_ctor_default ~mutual_name_map ctor
              | None ->
                let safe_indirect = List.find_opt (fun (_, _, _, src_ts) ->
                  let args = Seplist.to_list src_ts in
                  not (List.exists (src_t_is_directly_mutual [path]) args)
                ) ctors in
                (match safe_indirect with
                  | Some ctor -> render_ctor_default ~mutual_name_map ctor
                  | None ->
                    raise (Reporting_basic.err_general true Ast.Unknown
                      "Lean backend: inhabited_default_expr tier-1 variant disagrees with inhabited_needs_tier2 (internal)")))
          | Te_record (_, _, fields, _) when List.length mutual_paths > 1 ->
            let field_list = Seplist.to_list fields in
            let field_defaults = List.map (fun (_, _, _, src_t) -> default_value_inhabited ~mutual_name_map src_t) field_list in
            let type_name = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip (B.type_path_to_name name path))) in
            Output.flat [from_string type_name; from_string ".mk "; concat_str " " field_defaults]
          | _ -> generate_default_value_texp t)
      else
        (* Parameterized types: tier 1 covers nullary constructors only. *)
        Some (match t with
          | Te_variant (_, seplist) ->
            let ctors = Seplist.to_list seplist in
            (match List.find_opt (fun (_, _, _, src_ts) ->
              Seplist.to_list src_ts = []) ctors with
              | Some ctor -> render_ctor_default ~mutual_name_map ctor
              | None ->
                raise (Reporting_basic.err_general true Ast.Unknown
                  "Lean backend: inhabited_default_expr tier-1 parameterized disagrees with inhabited_needs_tier2 (internal)"))
          | _ ->
            raise (Reporting_basic.err_general true Ast.Unknown
              "Lean backend: inhabited_default_expr tier-1 non-variant parameterized disagrees with inhabited_needs_tier2 (internal)"))
    (* Type variable binding + type args for Inhabited instance header *)
    and inhabited_type_parts tnvar_list =
      let tnvar_list' =
        if tnvar_list = [] then emp
        else
          (* Unconstrained {a : Type} bindings. Tier-1 instances (nullary/
             safe ctors) need no [Inhabited a] constraints; tier-2 derived
             instances append their [Inhabited tv] binders separately
             (inhabited_bound_binders). *)
          let tvs = List.map (fun tv ->
            match tv with
            | Typed_ast.Tn_A (_, r, _) -> Types.Ty (Tyvar.from_rope r)
            | Typed_ast.Tn_N (_, r, _) -> Types.Nv (Nvar.from_rope r)
          ) tnvar_list in
          let_type_variables true (Types.TNset.of_list tvs)
      in
      let tnvar_names = concat_str " " @@ List.map (fun x -> from_string (tnvar_to_string x)) tnvar_list in
      let type_args =
        if List.length tnvar_list = 0 then emp
        else Output.flat [from_string " "; tnvar_names]
      in
      (tnvar_list', type_args)
    (* Tier 2: per-constructor bounded derivation (design note rules
       2-5). For each constructor
       whose fields are all derivably inhabitable, emit one bounded
       instance — the first at default priority, the rest at
       (priority := low), the LemLib Sum inl/inr pair precedent
       (lean-lib/LemLib.lean:90-91). Fail-closed: no usable constructor
       -> NO instance and NO fallback of any kind; the type is
       census-recorded Inh_none so any backend-visible demand on it is a
       generation-time error (inhabited_demand_check). The derivation
       itself was computed by lean_inhabited_prepass in DECLARATION
       order (emission runs fold_right, last-to-first); this function
       only renders the stored plan. *)
    and generate_tier2_inhabited (((name, _), tnvar_list, path, t, _)) : Output.t =
      let type_name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip (B.type_path_to_name name path))) in
      let name_out = lskips_t_to_output (B.type_path_to_name name path) in
      let (tnvar_list', type_args) = inhabited_type_parts tnvar_list in
      let emit_instances (bodies : (Output.t * string list) list) : Output.t =
        Output.flat (List.mapi (fun i (body, bounds) ->
          let inst_kw = if i = 0 then "instance" else "\ninstance (priority := low)" in
          Output.flat [
            from_string inst_kw; tnvar_list'; inhabited_bound_binders tnvar_list bounds;
            from_string " : Inhabited ("; name_out; type_args;
            from_string ") where\n  default := "; body;
          ]) bodies)
      in
      match inhabited_plan_lookup path, t with
        | (None | Some Plan_none), _ ->
          (* Fail-closed: no usable constructor -> no instance, no
             fallback of any kind. Demands error via inhabited_demand_check. *)
          emp
        | Some (Plan_variant usable), Te_variant (_, seplist) ->
          let ctors = Array.of_list (Seplist.to_list seplist) in
          emit_instances (List.map (fun (i, bounds) ->
            (render_ctor_default ctors.(i), bounds)) usable)
        | Some (Plan_record bounds), Te_record (_, _, fields, _) ->
          let field_list = Seplist.to_list fields in
          let field_defaults = List.map (fun (_, _, _, src_t) -> default_value_inhabited src_t) field_list in
          let body = Output.flat [from_string type_name_str; from_string ".mk "; concat_str " " field_defaults] in
          emit_instances [(body, bounds)]
        | _ ->
          raise (Reporting_basic.err_general true Ast.Unknown (Printf.sprintf
            "Lean backend: tier-2 Inhabited plan for type '%s' does not match its definition shape (internal pre-pass/emission mismatch)" type_name_str))
    (* Generate a single Inhabited instance (non-mutual or single-type blocks) *)
    and generate_inhabited_instance mutual_paths (((name, _), tnvar_list, path, t, _) as td) : Output.t =
      if skip_inhabited_for_type t path then emp
      else
      let name_out = lskips_t_to_output (B.type_path_to_name name path) in
      match inhabited_default_expr mutual_paths td with
        | None -> generate_tier2_inhabited td
        | Some default ->
          let (tnvar_list', type_args) = inhabited_type_parts tnvar_list in
          Output.flat [
            from_string "instance"; tnvar_list'; from_string " : Inhabited ("; name_out;
            type_args;
            from_string ") where\n  default := "; default;
          ]
    (* Generate mutual def + instance pairs for Inhabited on mutual type blocks.
       Uses `mutual def ... end` so forward references between defaults are allowed,
       then non-mutual `instance` declarations referencing those defs. *)
    and generate_inhabited_mutual mutual_paths ts_list : Output.t =
      (* Filter to types that need Inhabited *)
      let active = List.filter (fun (_, _, path, t, _) ->
        not (skip_inhabited_for_type t path)) ts_list in
      if active = [] then emp
      else if List.length active = 1 then
        (* Single type remaining: no need for mutual def *)
        generate_inhabited_instance mutual_paths (List.hd active)
      else
      (* Build path → type name mapping for mutual def references.
         Inside the mutual def block, we can't use `default` (Inhabited not defined yet),
         so direct mutual type args use TypeName.default_inhabited instead. *)
      let mutual_name_map = List.map (fun ((name, _), _, path, _, _) ->
        let type_name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip (B.type_path_to_name name path))) in
        (path, type_name_str)
      ) active in
      (* Compute defaults and split into tier 1 (real ctors, need mutual def)
         and tier 2 (per-constructor derived bounded instances
         rendered from the pre-pass plan). *)
      let typed_defaults = List.map (fun (((name, _), tnvar_list, path, _, _) as td) ->
        let type_name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip (B.type_path_to_name name path))) in
        let name_out = lskips_t_to_output (B.type_path_to_name name path) in
        let default_opt = inhabited_default_expr ~mutual_name_map mutual_paths td in
        (type_name_str, name_out, tnvar_list, default_opt, td)
      ) active in
      let tier1 = List.filter_map (fun (tns, no, tvs, d, td) ->
        match d with Some d -> Some (tns, no, tvs, d, td) | None -> None) typed_defaults in
      let tier2 = List.filter_map (fun (_, _, _, d, td) ->
        match d with None -> Some td | Some _ -> None) typed_defaults in
      (* Tier 1: mutual def block with real constructor defaults *)
      let mutual_block = if tier1 = [] then emp else
        let defs = List.map (fun (type_name_str, name_out, tnvar_list, default, _) ->
          let (tnvar_list', type_args) = inhabited_type_parts tnvar_list in
          Output.flat [
            from_string "def "; from_string type_name_str; from_string ".default_inhabited";
            tnvar_list'; from_string " : "; name_out; type_args;
            from_string " := "; default;
          ]
        ) tier1 in
        let instances = List.map (fun (type_name_str, _, tnvar_list, _, _) ->
          let (tnvar_list', type_args) = inhabited_type_parts tnvar_list in
          Output.flat [
            from_string "\ninstance"; tnvar_list'; from_string " : Inhabited (";
            from_string type_name_str; type_args;
            from_string ") where\n  default := "; from_string type_name_str;
            from_string ".default_inhabited";
          ]
        ) tier1 in
        Output.flat [
          from_string "mutual\n"; concat_str "\n" defs;
          from_string "\nend"; concat emp instances;
        ]
      in
      (* Tier 2: per-constructor derived instances (from the
         pre-pass plan), emitted in declaration order after the tier-1
         instances — so tier-2 bodies may resolve through every tier-1
         instance of the block and every EARLIER tier-2 sibling's
         instances, exactly as the pre-pass assumed. *)
      let tier2_instances = List.map (fun td ->
        Output.flat [from_string "\n"; generate_tier2_inhabited td]) tier2 in
      Output.flat [mutual_block; concat emp tier2_instances]
    and generate_beq_ord_instances ?(is_type1=false) ?(emit_deriving=true) ?derived_cmp ((name, _), tnvar_list, path, t, _) : Output.t =
      (* Skip instance generation for abbreviations, types with target reps,
         and types annotated with 'declare {lean} skip instances'. *)
      let skip_instances = match t with
        | Te_abbrev _ -> true
        | _ ->
          let l = Ast.Trans (false, "generate_beq_ord_instances", None) in
          let td = Types.type_defs_lookup l A.env.t_env path in
          (* Skip if declared with 'skip instances' for Lean *)
          Target.Targetset.mem Target.Target_lean td.Types.type_skip_instances ||
          Target.Targetmap.apply_target td.Types.type_target_rep
            (Target.Target_no_ident Target.Target_lean) <> None
      in
      if skip_instances then emp
      else
      match t with
        | Te_abbrev _ ->
          raise (Reporting_basic.err_general true Ast.Unknown
            "Lean backend: Te_abbrev in generate_beq_ord_instances should be unreachable (skip_instances handles it)")
        | _ ->
          let n = B.type_path_to_name name path in
          let o = lskips_t_to_output n in
          let tnvar_names = concat_str " " @@ List.map (fun x -> from_string (tnvar_to_string x)) tnvar_list in
          let type_args =
            if List.length tnvar_list = 0 then emp
            else Output.flat [from_string " "; tnvar_names]
          in
          (* If the type uses deriving BEq, Ord (emitted by tyexp), emit no
             BEq/Ord instances here. Mutual types normally can't use deriving
             (emit_deriving=false), but all-nullary enums in mutual blocks
             CAN derive — they have no args so no dependency on other types. *)
          let is_all_nullary = match t with
            | Te_variant (_, ctors) ->
              Seplist.for_all (fun (_, _, _, args) -> Seplist.to_list args = []) ctors
            | _ -> false
          in
          let has_deriving = (emit_deriving || is_all_nullary) && texp_can_derive_beq t
                             && not (texp_needs_ocaml_rank t) in
          let type_name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip n)) in
          let bare_tvs = from_string (merge_implicit_binders (String.concat "" (List.map (fun t ->
              String.concat "" [" {"; tnvar_to_string t; " : "; tnvar_kind t; "}"]) tnvar_list))) in
          (* Render " [Cls tv]" binders for the given tyvar names,
             in parameter-declaration order (the inhabited_bound_binders
             pattern applied to comparison classes). *)
          let cls_bounds cls (bounds : string list) : Output.t =
            Output.flat (List.filter_map (fun tv ->
              let tn = tnvar_to_string tv in
              if List.mem tn bounds then
                Some (Output.flat [from_string " ["; from_string cls; from_string " "; from_string tn; from_string "]"])
              else None) tnvar_list)
          in
          (* All Type-kind parameters — the bound set used for the
             deriving-bridge on PARAMETERIZED deriving types (Lean's own
             derived BEq/Ord instances carry per-parameter constraints). *)
          let all_ty_tvs = List.filter_map (fun tv ->
            match tv with
              | Typed_ast.Tn_A _ -> Some (tnvar_to_string tv)
              | Typed_ast.Tn_N _ -> None) tnvar_list in
          (* A residual instance has a loud failwithI body (axiom-free; it
             mirrors OCaml raising Invalid_argument when polymorphic
             comparison reaches a closure), naming its class. *)
          let residual_body cls reason =
            String.concat "" ["failwithI \"Lean backend: comparison residual: "; cls; " ("; type_name_str; "): "; reason; "\""] in
          let fn_reason = "type carries function-typed fields (OCaml polymorphic comparison raises on closures)" in
          (* A type without a derived comparison keeps a LOUD residual: it
             fails if, and only if, a comparison actually reaches it (as
             OCaml's compare does on closures). Function-typed fields are
             compared structurally down to the closure, so what remains is a
             shape the derivation cannot recurse through. *)
          let residual_reason =
            if texp_fn_fields t then fn_reason
            else "no derived structural comparison (a mutual sibling under a type head other than list/maybe/either/tuple); fails only if a comparison reaches it" in
          let residual_beq_ord reason priority_kw =
            (Output.flat [
              from_string priority_kw; bare_tvs; from_string " : BEq ("; o;
              type_args;
              from_string ") where\n  beq _ _ := "; from_string (residual_body "BEq" reason);
            ],
            Output.flat [
              from_string priority_kw; bare_tvs; from_string " : Ord ("; o;
              type_args;
              from_string ") where\n  compare _ _ := "; from_string (residual_body "Ord" reason);
            ])
          in
          let beq_instance, ord_instance =
            if has_deriving then (emp, emp)
            else if is_type1 then
              (* Type-1 universe (heterogeneous parameter counts in the
                 mutual block): FAIL-CLOSED. No residual instance is emitted
                 — the population is empty today, so any future Type-1 type
                 reaching instance emission is a loud generation-time error
                 naming the escape hatches, exactly like the Inhabited
                 path. *)
              raise (Reporting_basic.err_general true Ast.Unknown
                (Printf.sprintf
                  "Lean backend: cannot derive BEq/Ord instances for type '%s': heterogeneous type-parameter counts put its mutual block in the Type 1 universe, where the comparison classes are not defined; escape hatches: 'declare {lean} skip_instances type %s' plus hand-written Lean instances where demanded, or 'declare lean target_rep type %s' mapping it to a hand-written Lean type"
                  type_name_str type_name_str type_name_str))
            else match derived_cmp with
              | Some bounds ->
                (* REAL instances over the derived structural
                   comparison functions (emitted by
                   generate_derived_comparisons in this type's mutual
                   block). DEFAULT priority — the same standing Lean's own
                   `deriving BEq, Ord` instances get: LemLib's generic
                   default-priority bridges ([MapKeyType a] : BEq a,
                   [Eq0 a] : BEq a, [SetType a] : BEq a) would otherwise
                   shadow a low-priority real instance and complete
                   through the unconstrained failwithI fallback.
                   Hand-written override instance files still win: equal
                   priority resolves newest-declaration-first, and
                   override files import the generated module. *)
                (Output.flat [
                  from_string "\ninstance"; bare_tvs; cls_bounds "BEq" bounds;
                  from_string " : BEq ("; o; type_args;
                  from_string ") where\n  beq := "; from_string type_name_str; from_string ".beq_derived";
                ],
                Output.flat [
                  from_string "\ninstance"; bare_tvs; cls_bounds "Ord" bounds;
                  from_string " : Ord ("; o; type_args;
                  from_string ") where\n  compare := "; from_string type_name_str; from_string ".compare_derived";
                ])
              | None -> residual_beq_ord residual_reason "\ninstance (priority := low)"
          in
          (* There is no instance for a demand at an OPEN type variable: a
             generic definition that compares values of a parameterized type
             takes [Ord a]/[BEq a] binders instead (lean_cmp_prepass), so a
             demand the threading misses is a Lean compile error, never a
             runtime panic. *)
          (* SetType/Eq0/Ord0 are defined for (a : Type) only, skip for Type 1 *)
          if is_type1 then Output.flat [beq_instance; ord_instance]
          else
            (* SetType/Eq0/Ord0 (lem classes): bridge to the Lean BEq/Ord
               instances wherever those are real — derived-with-`deriving`
               (monomorphic: unconditional; parameterized: [BEq tv]/[Ord tv]
               bounds) or comparison-derived (bounds from the derivation
               plan). Residual types carry loud failwithI bodies.

               PRIORITY: the AUTO trio is emitted at the lattice's "auto"
               slot (lean_instance_kw_auto): strictly BELOW model-declared
               lem `instance` declarations and hand-written overrides
               (default = 1000), so a model's own Eq0/SetType/Ord0 wins by
               PRIORITY and not by declaration order (when both were at
               the default the model instance won only by
               newest-declaration-first order, which once let Cerberus's
               location-sensitive auto Eq0 for Symbol.identifier be chosen
               over the model's name-only one); strictly ABOVE the generic
               low(=100) bridges/defaults in LemLib/Basic_classes, so where
               no model instance exists the real auto trio still beats
               every default. Resolution probe:
               tests/comprehensive/test_instance_priority.lem
               (build-failing if the wrong instance wins). *)
            let real_trio (bounds : string list) (inst_kw : string) : Output.t =
              Output.flat [
                from_string inst_kw; bare_tvs; cls_bounds "Ord" bounds;
                from_string " : Lem_Basic_classes.SetType ("; o; type_args;
                from_string ") where\n  setElemCompare := defaultCompare";
                from_string inst_kw; bare_tvs; cls_bounds "BEq" bounds;
                from_string " : Lem_Basic_classes.Eq0 ("; o; type_args;
                from_string ") where\n  isEqual x y := x == y\n  isInequal x y := !(x == y)";
                from_string inst_kw; bare_tvs; cls_bounds "Ord" bounds;
                from_string " : Lem_Basic_classes.Ord0 ("; o; type_args;
                from_string ") where\n  compare := defaultCompare\n  isLess := defaultLess\n  isLessEqual := defaultLessEq\n  isGreater := defaultGreater\n  isGreaterEqual := defaultGreaterEq";
              ]
            in
            (* Trio for comparison-DERIVED types: bodies call the derived
               functions DIRECTLY (no `==`/defaultCompare instance
               indirection, which LemLib's generic default-priority
               bridges could reroute through a fallback). *)
            let derived_trio (bounds : string list) : Output.t =
              let bd = from_string type_name_str in
              let lem_of_cmp x y =
                Output.flat [
                  from_string "match "; bd; from_string ".compare_derived "; from_string x;
                  from_string " "; from_string y;
                  from_string " with | .lt => LemOrdering.LT | .eq => LemOrdering.EQ | .gt => LemOrdering.GT";
                ] in
              let bool_of_cmp x y arms =
                Output.flat [
                  from_string "match "; bd; from_string ".compare_derived "; from_string x;
                  from_string " "; from_string y; from_string (String.concat "" [" with "; arms]);
                ] in
              Output.flat [
                from_string lean_instance_kw_auto; bare_tvs; cls_bounds "Ord" bounds;
                from_string " : Lem_Basic_classes.SetType ("; o; type_args;
                from_string ") where\n  setElemCompare x y := "; lem_of_cmp "x" "y";
                from_string lean_instance_kw_auto; bare_tvs; cls_bounds "BEq" bounds;
                from_string " : Lem_Basic_classes.Eq0 ("; o; type_args;
                from_string ") where\n  isEqual := "; bd; from_string ".beq_derived";
                from_string "\n  isInequal x y := !("; bd; from_string ".beq_derived x y)";
                from_string lean_instance_kw_auto; bare_tvs; cls_bounds "Ord" bounds;
                from_string " : Lem_Basic_classes.Ord0 ("; o; type_args;
                from_string ") where\n  compare x y := "; lem_of_cmp "x" "y";
                from_string "\n  isLess x y := "; bool_of_cmp "x" "y" "| .lt => true | _ => false";
                from_string "\n  isLessEqual x y := "; bool_of_cmp "x" "y" "| .gt => false | _ => true";
                from_string "\n  isGreater x y := "; bool_of_cmp "x" "y" "| .gt => true | _ => false";
                from_string "\n  isGreaterEqual x y := "; bool_of_cmp "x" "y" "| .lt => false | _ => true";
              ]
            in
            let residual_trio reason inst_kw : Output.t =
              Output.flat [
                from_string inst_kw; bare_tvs; from_string " : Lem_Basic_classes.SetType ("; o;
                type_args;
                from_string ") where\n  setElemCompare _ _ := "; from_string (residual_body "SetType" reason);
                from_string inst_kw; bare_tvs; from_string " : Lem_Basic_classes.Eq0 ("; o;
                type_args;
                from_string ") where\n  isEqual _ _ := "; from_string (residual_body "Eq0" reason);
                from_string "\n  isInequal _ _ := "; from_string (residual_body "Eq0" reason);
                from_string inst_kw; bare_tvs; from_string " : Lem_Basic_classes.Ord0 ("; o;
                type_args;
                from_string ") where\n  compare _ _ := "; from_string (residual_body "Ord0" reason);
                from_string "\n  isLess _ _ := "; from_string (residual_body "Ord0" reason);
                from_string "\n  isLessEqual _ _ := "; from_string (residual_body "Ord0" reason);
                from_string "\n  isGreater _ _ := "; from_string (residual_body "Ord0" reason);
                from_string "\n  isGreaterEqual _ _ := "; from_string (residual_body "Ord0" reason);
              ]
            in
            Output.flat [
              beq_instance;
              ord_instance;
              (if has_deriving && tnvar_list = [] then real_trio [] lean_instance_kw_auto
               else if has_deriving then real_trio all_ty_tvs lean_instance_kw_auto
               else match derived_cmp with
                 | Some bounds -> derived_trio bounds
                 | None -> residual_trio residual_reason "\ninstance (priority := low)");
            ]
    (* ===== Derived structural comparisons for mutual blocks =====
       For every derivable type of a (homogeneous-parameter) mutual block,
       emit total mutual `beq_derived` / `compare_derived` functions plus
       the specialized container helpers structural recursion needs, then
       let generate_beq_ord_instances bridge the BEq/Ord/SetType/Eq0/Ord0
       instances onto them.

       PARITY CONVENTION (OCaml polymorphic (=) / compare, Cerberus's
       CerbStepInstances precedent):
       - equality is structural: same constructor + equal fields;
       - compare ranks constructors like the OCaml runtime
         (runtime/compare.c): NULLARY constructors are immediates and sort
         BELOW every non-nullary (block) constructor; within each class,
         declaration order; equal constructors compare fields left-to-right
         lexicographically (ctor_rank_ocaml encodes the two-class rank);
       - list: [] (immediate) < _::_ (block), then elementwise lex;
         maybe: None < Some; either: Left/inl < Right/inr — each matching
         the OCaml value representation of the corresponding lem library
         type;
       - leaf fields (no mutual sibling inside) compare through their Lean
         BEq/Ord instances. Leaf variants that mix nullary-after-block
         constructors no longer take Lean's `deriving Ord` (flat declaration
         index): every such variant is routed through this derivation
         (texp_needs_ocaml_rank), so the
         OCaml two-class rank holds at leaves too.

       FAIL-CLOSED: types whose comparison cannot be honestly derived
       (function-typed fields anywhere — where OCaml (=)/compare RAISE —
       or references to such siblings, or siblings under unsupported
       container heads) keep their loud residual instances, overridable
       by hand instance files. Underivability PROPAGATES: a "derived"
       body is never routed through a residual instance. *)
    and lean_output_str (o : Output.t) : string =
      Ulib.Text.to_string (to_rope (r"\"") lex_skip need_space o)
    and lean_typ_render (ty : Types.t) : string =
      lean_output_str (pat_typ (C.t_to_src_t ty))
    and generate_derived_comparisons ts_list : Output.t * (Path.t * string list) list =
      let d = A.env.t_env in
      let l = Ast.Trans (false, "generate_derived_comparisons", None) in
      let non_abbrev = List.filter (fun (_, _, _, t, _) ->
        match t with Te_abbrev _ -> false | _ -> true) ts_list in
      let skip_type path =
        let td = Types.type_defs_lookup l A.env.t_env path in
        Target.Targetset.mem Target.Target_lean td.Types.type_skip_instances ||
        Target.Targetmap.apply_target td.Types.type_target_rep
          (Target.Target_no_ident Target.Target_lean) <> None
      in
      let deriving_covered t = match t with
        | Te_variant (_, ctors) ->
          Seplist.for_all (fun (_, _, _, args) -> Seplist.to_list args = []) ctors
          && texp_can_derive_beq t
        | _ -> false
      in
      (* Candidates: (path, Lean type name, tnvar_list, ctors) with
         ctor = (Lean ctor name, field semantic types). Instance-backed
         block members (skip_instances / deriving-covered) are LEAVES;
         everything else that fails candidacy is a RESIDUAL sibling —
         referencing it poisons the referencing type (fail-closed). *)
      let candidates, residual0 =
        List.fold_right (fun (((name, _), tnvar_list, path, t, _)) (cs, os) ->
          if skip_type path then (cs, os)
          else if deriving_covered t then (cs, os)
          else if not (texp_can_derive_beq t) && not (texp_fn_fields t) then (cs, path :: os)
          else
            let type_name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip (B.type_path_to_name name path))) in
            (match t with
              | Te_variant (_, seplist) ->
                let ctors = List.map (fun ((cn, _), c_ref, _, args) ->
                  let cname = B.const_ref_to_name cn false c_ref in
                  let cn_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip cname)) in
                  (cn_str, List.map (fun (s : src_t) -> s.typ) (Seplist.to_list args))
                ) (Seplist.to_list seplist) in
                ((path, type_name_str, tnvar_list, ctors) :: cs, os)
              | Te_record (_, _, fields, _) ->
                let ctors = [("mk", List.map (fun (_, _, _, (s : src_t)) -> s.typ) (Seplist.to_list fields))] in
                ((path, type_name_str, tnvar_list, ctors) :: cs, os)
              | _ -> (cs, path :: os))
        ) non_abbrev ([], [])
      in
      (* Fixpoint: drop candidates with any underivable field shape;
         dropped candidates become residual siblings for the next round. *)
      let rec solve cands residual =
        let derived_map = List.map (fun (p, nm, _, _) -> (p, nm)) cands in
        let ok, bad = List.partition (fun (_, _, _, ctors) ->
          List.for_all (fun (_, args) ->
            List.for_all (fun ty ->
              not (lean_cmp_shape_is_bad (lean_cmp_shape d derived_map residual ty))) args) ctors)
          cands
        in
        if bad = [] then (ok, residual)
        else solve ok (List.map (fun (p, _, _, _) -> p) bad @ residual)
      in
      let derived, residual = solve candidates residual0 in
      if derived = [] then (emp, [])
      else begin
        let derived_map = List.map (fun (p, nm, _, _) -> (p, nm)) derived in
        let shape_of ty = lean_cmp_shape d derived_map residual ty in
        (* Bound tyvars of a type: Type-kind parameters free in some field
           (covers transitive needs — a sibling application's arguments are
           part of the field type), in parameter-declaration order. *)
        let bounds_of tnvar_list ctors =
          let fvs = List.fold_left (fun acc (_, args) ->
            List.fold_left (fun acc ty -> Types.TNset.union acc (Types.free_vars ty)) acc args)
            Types.TNset.empty ctors in
          let free_names = List.map (fun tnv -> Ulib.Text.to_string (Types.tnvar_to_rope tnv))
            (Types.TNset.elements fvs) in
          List.filter_map (fun tv ->
            match tv with
              | Typed_ast.Tn_A _ ->
                let nm = tnvar_to_string tv in
                if List.mem nm free_names then Some nm else None
              | Typed_ast.Tn_N _ -> None) tnvar_list
        in
        (* Helper-def machinery: one specialized def per (kind, container
           type), memoized per block, emitted inside the same mutual block
           (classical structural recursion — the CerbStepInstances
           beqLoadedValueList pattern, generated). *)
        let helper_defs : string list ref = ref [] in
        let helper_memo : (string, string) Hashtbl.t = Hashtbl.create 16 in
        let helper_ctr = ref 0 in
        let first_name = match derived with (_, nm, _, _) :: _ -> nm | [] -> assert false in
        (* {tv : Type} [Cls tv] / {nv : Nat} binders for the tyvars free in
           the given types (helper signatures). *)
        let tv_binders_of (tys : Types.t list) (cls : string) : string =
          let fvs = List.fold_left (fun acc ty -> Types.TNset.union acc (Types.free_vars ty))
            Types.TNset.empty tys in
          let bs = List.map (fun tnv ->
            let nm = Ulib.Text.to_string (Types.tnvar_to_rope tnv) in
            match tnv with
              | Types.Ty _ -> Printf.sprintf "{%s : Type} [%s %s]" nm cls nm
              | Types.Nv _ -> Printf.sprintf "{%s : Nat}" nm)
            (Types.TNset.elements fvs) in
          (match bs with [] -> "" | _ -> String.concat "" [" "; String.concat " " bs])
        in
        (* Build ctor-argument patterns; tuples destructure in-pattern.
           Returns (x-pattern, y-pattern, leaves = (xvar, yvar, shape)). *)
        let rec build_pats (ctr : int ref) (sh : cmp_shape) : string * string * (string * string * cmp_shape) list =
          match sh with
            | CStuple shs ->
              let parts = List.map (build_pats ctr) shs in
              (Printf.sprintf "(%s)" (String.concat ", " (List.map (fun (a, _, _) -> a) parts)),
               Printf.sprintf "(%s)" (String.concat ", " (List.map (fun (_, b, _) -> b) parts)),
               List.concat_map (fun (_, _, ls) -> ls) parts)
            | _ ->
              incr ctr;
              let x = Printf.sprintf "x%d" !ctr and y = Printf.sprintf "y%d" !ctr in
              (x, y, [(x, y, sh)])
        in
        let rec beq_leaf (x, y, sh) : string =
          match sh with
            | CSleaf -> Printf.sprintf "%s == %s" x y
            | CSsibling nm -> Printf.sprintf "%s.beq_derived %s %s" nm x y
            | CSlist (et, esh) -> Printf.sprintf "%s %s %s" (helper "beq" (CSlist (et, esh))) x y
            | CSoption (et, esh) -> Printf.sprintf "%s %s %s" (helper "beq" (CSoption (et, esh))) x y
            | CSsum (a, b) -> Printf.sprintf "%s %s %s" (helper "beq" (CSsum (a, b))) x y
            | CSfn -> Printf.sprintf "lemFunctionalBeq %s %s" x y
            | CStuple _ | CSbad _ -> assert false (* destructured / fail-closed upstream *)
        and cmp_leaf (x, y, sh) : string =
          match sh with
            | CSleaf -> Printf.sprintf "Ord.compare %s %s" x y
            | CSsibling nm -> Printf.sprintf "%s.compare_derived %s %s" nm x y
            | CSlist (et, esh) -> Printf.sprintf "%s %s %s" (helper "cmp" (CSlist (et, esh))) x y
            | CSoption (et, esh) -> Printf.sprintf "%s %s %s" (helper "cmp" (CSoption (et, esh))) x y
            | CSsum (a, b) -> Printf.sprintf "%s %s %s" (helper "cmp" (CSsum (a, b))) x y
            | CSfn -> Printf.sprintf "lemFunctionalCompare %s %s" x y
            | CStuple _ | CSbad _ -> assert false
        and beq_conj (leaves : (string * string * cmp_shape) list) : string =
          match leaves with
            | [] -> "true"
            | _ -> String.concat " && " (List.map beq_leaf leaves)
        and cmp_chain (leaves : (string * string * cmp_shape) list) : string =
          match leaves with
            | [] -> "Ordering.eq"
            | [lf] -> cmp_leaf lf
            | lf :: rest ->
              Printf.sprintf "(match %s with | .lt => Ordering.lt | .gt => Ordering.gt | .eq => %s)"
                (cmp_leaf lf) (cmp_chain rest)
        (* Named helper for a container shape; generated on first demand. *)
        and helper (kind : string) (sh : cmp_shape) : string =
          let key = String.concat "" [kind; "|"; (match sh with
            | CSlist (et, _) -> String.concat "" ["list|"; lean_typ_render et]
            | CSoption (et, _) -> String.concat "" ["option|"; lean_typ_render et]
            | CSsum ((lt_, _), (rt_, _)) -> String.concat "" ["sum|"; lean_typ_render lt_; "|"; lean_typ_render rt_]
            | _ -> assert false)]
          in
          match Hashtbl.find_opt helper_memo key with
            | Some nm -> nm
            | None ->
              incr helper_ctr;
              let nm = Printf.sprintf "%s.%s_deriv_aux%d" first_name kind !helper_ctr in
              Hashtbl.add helper_memo key nm;
              (* Elements destructure via build_pats, so tuple-shaped
                 elements (e.g. List ((pattern × pexpr))) compare
                 componentwise inside the helper's own arm. *)
              let elem kind0 esh =
                let ctr = ref 0 in
                let (px, py, leaves) = build_pats ctr esh in
                (px, py, (if kind0 = "beq" then beq_conj leaves else cmp_chain leaves))
              in
              let def_text =
                match sh, kind with
                  | CSlist (et, esh), "beq" ->
                    let ety = lean_typ_render et in
                    let (px, py, body) = elem "beq" esh in
                    Printf.sprintf
                      "def %s%s (cmpx_ cmpy_ : List (%s)) : Bool := match cmpx_, cmpy_ with\n  | [], [] => true\n  | %s :: xs0, %s :: ys0 => %s && %s xs0 ys0\n  | _, _ => false\ntermination_by structural cmpx_"
                      nm (tv_binders_of [et] "BEq") ety
                      px py body nm
                  | CSlist (et, esh), "cmp" ->
                    let ety = lean_typ_render et in
                    let (px, py, body) = elem "cmp" esh in
                    Printf.sprintf
                      "def %s%s (cmpx_ cmpy_ : List (%s)) : Ordering := match cmpx_, cmpy_ with\n  | [], [] => Ordering.eq\n  | [], _ :: _ => Ordering.lt\n  | _ :: _, [] => Ordering.gt\n  | %s :: xs0, %s :: ys0 => (match %s with | .lt => Ordering.lt | .gt => Ordering.gt | .eq => %s xs0 ys0)\ntermination_by structural cmpx_"
                      nm (tv_binders_of [et] "Ord") ety
                      px py body nm
                  | CSoption (et, esh), "beq" ->
                    let ety = lean_typ_render et in
                    let (px, py, body) = elem "beq" esh in
                    Printf.sprintf
                      "def %s%s (cmpx_ cmpy_ : Option (%s)) : Bool := match cmpx_, cmpy_ with\n  | none, none => true\n  | some %s, some %s => %s\n  | _, _ => false\ntermination_by structural cmpx_"
                      nm (tv_binders_of [et] "BEq") ety
                      px py body
                  | CSoption (et, esh), "cmp" ->
                    let ety = lean_typ_render et in
                    let (px, py, body) = elem "cmp" esh in
                    Printf.sprintf
                      "def %s%s (cmpx_ cmpy_ : Option (%s)) : Ordering := match cmpx_, cmpy_ with\n  | none, none => Ordering.eq\n  | none, some _ => Ordering.lt\n  | some _, none => Ordering.gt\n  | some %s, some %s => %s\ntermination_by structural cmpx_"
                      nm (tv_binders_of [et] "Ord") ety
                      px py body
                  | CSsum ((lt_, shl), (rt_, shr)), "beq" ->
                    let lty = lean_typ_render lt_ and rty = lean_typ_render rt_ in
                    let (plx, ply, lbody) = elem "beq" shl in
                    let (prx, pry, rbody) = elem "beq" shr in
                    Printf.sprintf
                      "def %s%s (cmpx_ cmpy_ : Sum (%s) (%s)) : Bool := match cmpx_, cmpy_ with\n  | Sum.inl %s, Sum.inl %s => %s\n  | Sum.inr %s, Sum.inr %s => %s\n  | _, _ => false\ntermination_by structural cmpx_"
                      nm (tv_binders_of [lt_; rt_] "BEq") lty rty
                      plx ply lbody prx pry rbody
                  | CSsum ((lt_, shl), (rt_, shr)), "cmp" ->
                    let lty = lean_typ_render lt_ and rty = lean_typ_render rt_ in
                    let (plx, ply, lbody) = elem "cmp" shl in
                    let (prx, pry, rbody) = elem "cmp" shr in
                    Printf.sprintf
                      "def %s%s (cmpx_ cmpy_ : Sum (%s) (%s)) : Ordering := match cmpx_, cmpy_ with\n  | Sum.inl %s, Sum.inl %s => %s\n  | Sum.inl _, Sum.inr _ => Ordering.lt\n  | Sum.inr _, Sum.inl _ => Ordering.gt\n  | Sum.inr %s, Sum.inr %s => %s\ntermination_by structural cmpx_"
                      nm (tv_binders_of [lt_; rt_] "Ord") lty rty
                      plx ply lbody prx pry rbody
                  | _ -> assert false
              in
              helper_defs := def_text :: !helper_defs;
              nm
        in
        (* Signature pieces per type. *)
        let sig_of tnvar_list bounds cls =
          let binders = String.concat "" (List.map (fun tv ->
            let nm = tnvar_to_string tv in
            let base = Printf.sprintf " {%s : %s}" nm (tnvar_kind tv) in
            if List.mem nm bounds then Printf.sprintf "%s [%s %s]" base cls nm else base)
            tnvar_list) in
          let args = String.concat "" (List.map (fun tv -> String.concat "" [" "; tnvar_to_string tv]) tnvar_list) in
          (merge_implicit_binders binders, args)
        in
        (* Two-class OCaml rank def (only needed with >1 constructor). *)
        let rank_def type_name tnvar_list ctors : string =
          let nullary_rank = ref 0 in
          let nnullary = List.length (List.filter (fun (_, args) -> args = []) ctors) in
          let block_rank = ref 0 in
          let arms = List.map (fun (cn, args) ->
            let rank =
              if args = [] then (let r0 = !nullary_rank in incr nullary_rank; r0)
              else (let r0 = nnullary + !block_rank in incr block_rank; r0)
            in
            let wilds = String.concat "" (List.map (fun _ -> " _") args) in
            Printf.sprintf "  | .%s%s => %d" cn wilds rank) ctors in
          let (binders, args) = sig_of tnvar_list [] "" in
          Printf.sprintf
            "/- lem: constructor rank for OCaml's polymorphic compare: nullary\n   constructors (immediates) sort below non-nullary ones (blocks);\n   declaration order within each group. -/\ndef %s.ctor_rank_ocaml%s : %s%s → Nat\n%s"
            type_name binders type_name args (String.concat "\n" arms)
        in
        let beq_def (type_name, tnvar_list, bounds, ctors) : string =
          let (binders, args) = sig_of tnvar_list bounds "BEq" in
          let arms = List.map (fun (cn, argtys) ->
            let ctr = ref 0 in
            let parts = List.map (fun ty -> build_pats ctr (shape_of ty)) argtys in
            let px = String.concat " " (List.map (fun (a, _, _) -> a) parts) in
            let py = String.concat " " (List.map (fun (_, b, _) -> b) parts) in
            let leaves = List.concat_map (fun (_, _, ls) -> ls) parts in
            let sp = if argtys = [] then "" else " " in
            Printf.sprintf "  | .%s%s%s, .%s%s%s => %s" cn sp px cn sp py (beq_conj leaves)) ctors in
          let fallback = if List.length ctors > 1 then ["  | _, _ => false"] else [] in
          Printf.sprintf "def %s.beq_derived%s (cmpx_ cmpy_ : %s%s) : Bool := match cmpx_, cmpy_ with\n%s\ntermination_by structural cmpx_"
            type_name binders type_name args
            (String.concat "\n" (arms @ fallback))
        in
        let cmp_def (type_name, tnvar_list, bounds, ctors) : string =
          let (binders, args) = sig_of tnvar_list bounds "Ord" in
          let arms = List.filter_map (fun (cn, argtys) ->
            if argtys = [] then None  (* nullary pairs: rank fallback yields .eq *)
            else begin
              let ctr = ref 0 in
              let parts = List.map (fun ty -> build_pats ctr (shape_of ty)) argtys in
              let px = String.concat " " (List.map (fun (a, _, _) -> a) parts) in
              let py = String.concat " " (List.map (fun (_, b, _) -> b) parts) in
              let leaves = List.concat_map (fun (_, _, ls) -> ls) parts in
              Some (Printf.sprintf "  | .%s %s, .%s %s => %s" cn px cn py (cmp_chain leaves))
            end) ctors in
          let fallback =
            if List.length ctors > 1 then
              [Printf.sprintf "  | xg, yg => Ord.compare (%s.ctor_rank_ocaml xg) (%s.ctor_rank_ocaml yg)" type_name type_name]
            else [] in
          Printf.sprintf "def %s.compare_derived%s (cmpx_ cmpy_ : %s%s) : Ordering := match cmpx_, cmpy_ with\n%s\ntermination_by structural cmpx_"
            type_name binders type_name args
            (String.concat "\n" (arms @ fallback))
        in
        (* Render: rank defs (non-recursive, before the block), then the
           mutual block. Type-def bodies are rendered FIRST so helper
           demand is populated; helpers can demand further helpers. *)
        let per_type = List.map (fun (path, nm, tnvar_list, ctors) ->
          (path, nm, tnvar_list, bounds_of tnvar_list ctors, ctors)) derived in
        let type_defs_text = List.concat_map (fun (_, nm, tvs, bounds, ctors) ->
          [beq_def (nm, tvs, bounds, ctors); cmp_def (nm, tvs, bounds, ctors)]) per_type in
        let rank_defs_text = List.filter_map (fun (_, nm, tvs, _, ctors) ->
          if List.length ctors > 1 then Some (rank_def nm tvs ctors) else None) per_type in
        let all_mutual = type_defs_text @ List.rev !helper_defs in
        let text = String.concat "" [
          "\n/- lem: equality and comparison for these types, matching OCaml's\n";
          "   polymorphic (=) and compare: structural equality; nullary constructors\n";
          "   before non-nullary ones, declaration order within each group; fields\n";
          "   compared left to right; leaf fields by their Lean BEq/Ord instances. -/\n";
          (match rank_defs_text with [] -> "" | rs -> String.concat "" [String.concat "\n" rs; "\n"]);
          "mutual\n";
          String.concat "\n" all_mutual;
          "\nend\n";
        ] in
        (from_string text, List.map (fun (path, _, _, bounds, _) -> (path, bounds)) per_type)
      end
    (* ===== Derived computable SIZE functions
       (mechanism comment at lean_size_shape, top level). For a recursive
       block of generated inductives, one mutual block: `t.lemSize` per
       member type and `<first>.lemSize_aux<k>` per container element
       shape (list/option/sum, memoized per block) — the derived-comparison
       machinery's shape, `termination_by structural` on every member that
       makes a block call (a member with none is a plain def: Lean warns
       on an unused clause). The census (lean_size_block) and this emitter
       run the same analysis on the same block, so `lemSize x` in a
       measure resolves exactly to what is emitted. *)
    and generate_lem_size ts_list : Output.t =
      match lean_size_block A.env !St.current_module_name ts_list with
      | Error _ -> emp
      | Ok members ->
        let d = A.env.t_env in
        let l = match ts_list with ((_, l0), _, _, _, _) :: _ -> l0 | [] -> Ast.Trans (false, "generate_lem_size", None) in
        let siblings = List.map (fun (p, nm, _, _) -> (p, nm)) members in
        let shape_of ty = lean_size_shape d siblings ty in
        let collides nm =
          nm = lean_reserved_size_name || lean_starts_with lean_reserved_size_aux_prefix nm in
        (* fail-closed: the derived names live in the type's namespace,
           as constructors (and mutual-block record accessors) do *)
        List.iter (fun (_, tnm, _, ctors) ->
            List.iter (fun (cn, _) ->
                if collides cn then
                  raise (Reporting_basic.err_general true l
                    (Printf.sprintf
                      "Lean backend: constructor `%s` of type `%s` collides with the backend-derived size function `%s.lemSize` / its helpers `%s.lemSize_aux<k>` (the names are reserved in every generated type's namespace; rename the constructor)"
                      cn tnm tnm tnm))) ctors) members;
        List.iter (fun ((n0, _), _, path, t, _) ->
            match t with
            | Te_record (_, _, fields, _) ->
              let tnm = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip (B.type_path_to_name n0 path))) in
              List.iter (fun ((fname, _), f_ref, _, _) ->
                  let fnm = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip (B.const_ref_to_name fname false f_ref))) in
                  if collides fnm then
                    raise (Reporting_basic.err_general true l
                      (Printf.sprintf
                        "Lean backend: field `%s` of record type `%s` collides with the backend-derived size function `%s.lemSize` / its helpers `%s.lemSize_aux<k>` (the names are reserved in every generated type's namespace; rename the field)"
                        fnm tnm tnm tnm))) (Seplist.to_list fields)
            | _ -> ()) ts_list;
        let first_name = match members with (_, nm, _, _) :: _ -> nm | [] -> assert false in
        let helper_defs : string list ref = ref [] in
        let helper_memo : (string, string) Hashtbl.t = Hashtbl.create 16 in
        let helper_ctr = ref 0 in
        let tv_binders_of (tys : Types.t list) : string =
          let fvs = List.fold_left (fun acc ty -> Types.TNset.union acc (Types.free_vars ty))
            Types.TNset.empty tys in
          let bs = List.map (fun tnv ->
            let nm = Ulib.Text.to_string (Types.tnvar_to_rope tnv) in
            match tnv with
              | Types.Ty _ -> Printf.sprintf "{%s : Type}" nm
              | Types.Nv _ -> Printf.sprintf "{%s : Nat}" nm)
            (Types.TNset.elements fvs) in
          (match bs with [] -> "" | _ -> merge_implicit_binders (String.concat "" [" "; String.concat " " bs])) in
        (* pattern for one field + the size terms its subterms contribute *)
        let rec build (ctr : int ref) (sh : cmp_shape) : string * string list =
          match sh with
            | CSleaf -> ("_", [])
            | CStuple shs ->
              let parts = List.map (build ctr) shs in
              (Printf.sprintf "(%s)" (String.concat ", " (List.map fst parts)),
               List.concat_map snd parts)
            | CSsibling nm ->
              incr ctr; let x = Printf.sprintf "x%d" !ctr in (x, [Printf.sprintf "%s.lemSize %s" nm x])
            | CSlist _ | CSoption _ | CSsum _ ->
              incr ctr; let x = Printf.sprintf "x%d" !ctr in (x, [Printf.sprintf "%s %s" (helper sh) x])
            | CSbad _ | CSfn ->
              (* lean_size_shape never produces either (a function-typed
                 field is a leaf of size 0 there) *)
              raise (Reporting_basic.err_general true l
                "Lean backend: internal error — the derived-size builder met a shape lean_size_shape never produces (CSbad/CSfn)")
        and sum_terms (terms : string list) : string =
          String.concat "" (List.map (fun t -> String.concat "" [" + "; t]) terms)
        and helper (sh : cmp_shape) : string =
          let key = match sh with
            | CSlist (et, _) -> String.concat "" ["list|"; lean_typ_render et]
            | CSoption (et, _) -> String.concat "" ["option|"; lean_typ_render et]
            | CSsum ((lt_, _), (rt_, _)) -> String.concat "" ["sum|"; lean_typ_render lt_; "|"; lean_typ_render rt_]
            | _ -> assert false in
          match Hashtbl.find_opt helper_memo key with
            | Some nm -> nm
            | None ->
              incr helper_ctr;
              let nm = Printf.sprintf "%s.lemSize_aux%d" first_name !helper_ctr in
              Hashtbl.add helper_memo key nm;
              let def_text =
                match sh with
                  | CSlist (et, esh) ->
                    let (px, terms) = build (ref 0) esh in
                    Printf.sprintf
                      "def %s%s (sizex_ : List (%s)) : Nat := match sizex_ with\n  | [] => 0\n  | %s :: xs0 => 1%s + %s xs0\ntermination_by structural sizex_"
                      nm (tv_binders_of [et]) (lean_typ_render et) px (sum_terms terms) nm
                  | CSoption (et, esh) ->
                    let (px, terms) = build (ref 0) esh in
                    Printf.sprintf
                      "def %s%s (sizex_ : Option (%s)) : Nat := match sizex_ with\n  | none => 0\n  | some %s => 1%s\ntermination_by structural sizex_"
                      nm (tv_binders_of [et]) (lean_typ_render et) px (sum_terms terms)
                  | CSsum ((lt_, shl), (rt_, shr)) ->
                    let (plx, lterms) = build (ref 0) shl in
                    let (prx, rterms) = build (ref 0) shr in
                    Printf.sprintf
                      "def %s%s (sizex_ : Sum (%s) (%s)) : Nat := match sizex_ with\n  | Sum.inl %s => 1%s\n  | Sum.inr %s => 1%s\ntermination_by structural sizex_"
                      nm (tv_binders_of [lt_; rt_]) (lean_typ_render lt_) (lean_typ_render rt_)
                      plx (sum_terms lterms) prx (sum_terms rterms)
                  | _ -> assert false in
              helper_defs := def_text :: !helper_defs;
              nm
        in
        let size_def (type_name, tnvar_list, ctors) : string =
          let binders = String.concat "" (List.map (fun tv ->
              Printf.sprintf " {%s : %s}" (tnvar_to_string tv) (tnvar_kind tv)) tnvar_list) in
          let args = String.concat "" (List.map (fun tv -> String.concat "" [" "; tnvar_to_string tv]) tnvar_list) in
          let recursive_here = ref false in
          let arms = List.map (fun (cn, argtys) ->
              let ctr = ref 0 in
              let parts = List.map (fun ty -> build ctr (shape_of ty)) argtys in
              let terms = List.concat_map snd parts in
              if terms <> [] then recursive_here := true;
              let sp = if argtys = [] then "" else " " in
              Printf.sprintf "  | .%s%s%s => 1%s" cn sp (String.concat " " (List.map fst parts)) (sum_terms terms))
            ctors in
          Printf.sprintf "def %s.lemSize%s (sizex_ : %s%s) : Nat := match sizex_ with\n%s%s"
            type_name binders type_name args (String.concat "\n" arms)
            (if !recursive_here then "\ntermination_by structural sizex_" else "")
        in
        (* type defs first (they populate the helper demand), helpers after *)
        let type_defs_text = List.map (fun (_, nm, tvs, ctors) -> size_def (nm, tvs, ctors)) members in
        let all_defs = type_defs_text @ List.rev !helper_defs in
        let body = String.concat "\n" all_defs in
        let text = String.concat "" [
          "\n/- lem: computable structural size `lemSize x`, for fuel measures: one\n";
          "   per constructor node of these types and per non-nullary container\n";
          "   constructor (`::`/`some`/`inl`/`inr`); tuples are transparent; every\n";
          "   other field counts 0. -/\n";
          (if List.length all_defs > 1 then String.concat "" ["mutual\n"; body; "\nend\n"]
           else String.concat "" [body; "\n"])
        ] in
        from_string text
    and generate_default_values ts : Output.t =
      let ts = Seplist.to_list ts in
      (* In library modules, skip instance generation for opaque types
         (zero-constructor inductives like phantom types ty1..ty4096).
         These types carry only type-level information (e.g., bit widths
         via Size) and are never used as data, so no instance is emitted
         for them.
         In user modules, opaque types (e.g., tid, location in cmm.lem) may
         appear as constructor arguments, so downstream types need their
         BEq/Ord instances for deriving to work. *)
      let is_lib = is_library_module !St.current_module_name in
      let ts = if is_lib then List.filter (fun (_, _, _, t, _) -> t <> Te_opaque) ts else ts in
      (* Treat each single type like a mutual block of one, so self-referential
         constructors (e.g. Unop : op → op0 → op1 → op1) are detected and
         avoided when generating the Inhabited instance. *)
      let mapped = List.map (fun (((_, _), _, path, _, _) as t) ->
        generate_inhabited_instance [path] t) ts in
      let beq_instances = List.map (fun (((_, _), _, _, t, _) as td) ->
        if (texp_needs_ocaml_rank t && texp_can_derive_beq t) || texp_fn_fields t then
          (* OCaml constructor rank for a single mixed-order variant — a
             mutual block of one through the derivation; likewise a type
             with function-typed fields. *)
          let (cmp_defs, derived_cmp) = derived_comparison_single td in
          Output.flat [cmp_defs; generate_beq_ord_instances ~emit_deriving:false ?derived_cmp td]
        else generate_beq_ord_instances td) ts in
        Output.flat [concat_str "\n" mapped; concat emp beq_instances; generate_lem_size ts]
    (* Run the derived-comparison generator on a single type
       whose constructor order needs the OCaml rank, fail-closed. A shape
       the derivation cannot recurse through (a self-reference under a
       head other than list/maybe/either/tuple) would leave the type with
       a residual (panicking) instance where OCaml compares fine, and
       `deriving Ord` would compute the WRONG order — neither is
       acceptable, so the type is refused with the workarounds named. *)
    and derived_comparison_single (((name, _), _, path, _, _) as td) : Output.t * string list option =
      let skip =
        let l = Ast.Trans (false, "derived_comparison_single", None) in
        let tdescr = Types.type_defs_lookup l A.env.t_env path in
        Target.Targetset.mem Target.Target_lean tdescr.Types.type_skip_instances ||
        Target.Targetmap.apply_target tdescr.Types.type_target_rep
          (Target.Target_no_ident Target.Target_lean) <> None in
      if skip then (emp, None)
      else begin
        let (cmp_defs, derived_info) = generate_derived_comparisons [td] in
        match List.find_opt (fun (p, _) -> Path.compare p path = 0) derived_info with
        | Some (_, bounds) -> (cmp_defs, Some bounds)
        | None ->
          raise (Reporting_basic.err_general true Ast.Unknown
            (Printf.sprintf
              "Lean backend: type '%s' declares a nullary constructor after a non-nullary one (OCaml polymorphic compare ranks nullary constructors below block constructors, Lean's `deriving Ord` ranks by declaration index) and its constructor fields reference the type under a head the derived comparison cannot recurse through (only list/maybe/either/tuples are supported) — emitting `deriving Ord` would compute a different order than the OCaml reference. Provide a hand-written Ord instance (`declare {lean} skip_instances type %s`) or restructure the field"
              (Name.to_string (Name.strip_lskip name)) (Name.to_string (Name.strip_lskip name))))
      end
    and generate_default_values_mutual ts : Output.t =
      let ts_list = Seplist.to_list ts in
      let is_lib = is_library_module !St.current_module_name in
      let ts_list = if is_lib then List.filter (fun (_, _, _, t, _) -> t <> Te_opaque) ts_list else ts_list in
      (* Filter out abbreviations for mutual_paths, is_type1, and emit_deriving decisions.
         Abbreviations don't participate in mutual recursion or instance generation. *)
      let non_abbrev = List.filter (fun (_, _, _, t, _) ->
        match t with Te_abbrev _ -> false | _ -> true) ts_list in
      let mutual_paths = List.map (fun ((_, _), _, path, _, _) -> path) non_abbrev in
      (* Check if the non-abbreviation types have heterogeneous param counts *)
      let param_counts = List.map (fun (_, ty_vars, _, _, _) -> List.length ty_vars) non_abbrev in
      let is_type1 = match param_counts with
        | [] -> false
        | x :: xs -> not (List.for_all (fun y -> y = x) xs)
      in
      let inhabited_output =
        if List.length non_abbrev > 1 then
          generate_inhabited_mutual mutual_paths ts_list
        else
          let mapped = List.map (generate_inhabited_instance mutual_paths) ts_list in
          concat_str "\n" mapped
      in
      (* If only 1 non-abbreviation type remains, it was rendered with deriving
         (not as a mutual block), so emit_deriving:true to avoid duplicate instances. *)
      let emit_deriving = List.length non_abbrev <= 1 in
      (* A block of one whose single variant needs the OCaml rank goes
         through the derivation like the single-type path. *)
      let single_needs_rank = match non_abbrev with
        | [(_, _, _, t, _)] -> (texp_needs_ocaml_rank t && texp_can_derive_beq t) || texp_fn_fields t
        | _ -> false in
      (* Derived structural comparisons for the block's derivable types
         (real mutual beq/compare defs; fail-closed residual for the
         rest). Homogeneous-parameter multi-type blocks only: single-type
         blocks keep the single-type emission, and Type-1 (indexed)
         blocks are a fail-closed generation-time error in
         generate_beq_ord_instances. *)
      let (cmp_defs, derived_info) =
        if single_needs_rank then
          (match List.find_opt (fun (_, _, _, t, _) -> texp_needs_ocaml_rank t || texp_fn_fields t) non_abbrev with
           | Some td ->
             let (o, bounds) = derived_comparison_single td in
             let (_, _, path, _, _) = td in
             (o, match bounds with Some b -> [(path, b)] | None -> [])
           | None -> (emp, []))
        else if is_type1 || emit_deriving then (emp, [])
        else generate_derived_comparisons ts_list
      in
      let beq_instances = List.map (fun (((_, _), _, path, _, _) as td) ->
        let derived_cmp =
          Option.map snd (List.find_opt (fun (p, _) -> Path.compare p path = 0) derived_info) in
        generate_beq_ord_instances ~is_type1 ~emit_deriving ?derived_cmp td) ts_list in
        Output.flat [inhabited_output; from_string "\n"; cmp_defs; concat emp beq_instances; generate_lem_size ts_list]
    (* L_undefined renders as failwithI (mirroring OCaml's `failwith m`,
       src/backend.ml:864), never as an opaque inhabitant or a silent
       default. *)
      ;;
end
;;


module CdsetE = Util.ExtraSet(Types.Cdset)

module LeanBackend (A : sig val avoid : var_avoid_f option;; val env : env;; val dir : string end) =
  struct

    (* Main definition processor: emits def output with location comments.
       Intentionally parallel to defs_extra below — they share the module
       setup but differ in which method they call (C.def vs C.def_extra)
       and whether location comments are prepended. Unifying them would
       require first-class modules which adds more complexity than the
       duplication costs. *)
    let rec defs inside_instance inside_module (ds : def list) =
        List.fold_right (fun (((d, s), l, lenv):def) y ->
          let ue = add_def_entities (Target_no_ident Target_lean) true empty_used_entities ((d,s),l,lenv) in
          let callback = defs false true in
          let module C = LeanBackendAux (
            struct
              let avoid = A.avoid;;
              let env = {A.env with local_env = lenv};;
              let ascii_rep_set = CdsetE.from_list ue.used_consts;;
              let dir = A.dir;;
            end)
          in
          let (before_out, d') = Backend_common.def_add_location_comment ((d,s),l,lenv) in
          before_out ^
          match s with
            | None   -> C.def inside_instance callback inside_module d' ^ y
            | Some s -> C.def inside_instance callback inside_module d' ^ ws s ^ y
        ) ds emp
    (* Auxiliary file processor: emits def_extra output without location comments. *)
    and defs_extra inside_instance inside_module (ds: def list) =
        List.fold_right (fun (((d, s), l, lenv):def) y ->
          let ue = add_def_entities (Target_no_ident Target_lean) true empty_used_entities ((d,s),l,lenv) in
          let module C = LeanBackendAux (
            struct
              let avoid = A.avoid;;
              let env = {A.env with local_env = lenv};;
              let ascii_rep_set = CdsetE.from_list ue.used_consts;;
              let dir = A.dir;;
            end)
          in
          let callback = defs false true in
          match s with
            | None   -> C.def_extra inside_instance callback inside_module d ^ y
            | Some s -> C.def_extra inside_instance callback inside_module d ^ ws s ^ y
        ) ds emp
    ;;

    (* --- Import and namespace management ---
       Library modules: wrapped in 'namespace Lem_ModuleName ... end' with imports at top.
       User modules: no namespace wrapper; automatically open all transitive library
       namespaces so types/classes from Pervasives etc. are in scope.
       Abbrev definitions may be deferred (St.pending_abbrevs) until after their
       dependencies are defined (e.g., abbrev mword after class Size). *)
    let lean_defs ((ds : def list), end_lex_skips) =
      St.reset_per_file ();
      lean_sorry_rep_check A.env;
      (* Set callback for per-file CR_simple import collection *)
      Backend_common.on_cr_simple_applied := collect_cr_simple_import;
      (* Note: St.mutual_records is NOT reset — [invocation] lifetime: it
         accumulates across files so that cross-file record updates on
         mutual-block records are detected. *)
      (* Pre-collect local module names before main processing, because
         defs uses fold_right (processes last-to-first). Without this,
         'open Operators' would be processed before 'module Operators',
         causing a spurious import. *)
      (* Recursively collect local module names including nested ones *)
      let rec collect_local_modules (ds : def list) : string list =
        List.concat_map (fun (((d, _), _, _) : def) ->
          match d with
          | Module (_, (name, _), _, _, _, defs, _) ->
            let name_str = Ulib.Text.to_string (Name.to_rope (Name.strip_lskip name)) in
            name_str :: collect_local_modules defs
          | _ -> []
        ) ds
      in
      St.local_modules := collect_local_modules ds;
      (* Pre-collect mutual record type names. Type_def blocks with >1 member
         that contain Te_record entries will render records as inductives.
         We need this list before defs runs (fold_right = last-to-first). *)
      St.mutual_records := !St.mutual_records @ List.concat_map (fun (((d, _), _, _) : def) ->
        match d with
        | Type_def (_, defs) when Seplist.length defs > 1 ->
            let all = Seplist.to_list defs in
            let non_abbrev = List.filter (fun (_, _, _, ty, _) ->
              match ty with Te_abbrev _ -> false | _ -> true
            ) all in
            if List.length non_abbrev > 1 && mutual_block_records_as_inductives non_abbrev then
              List.filter_map (fun (_, _, path, ty, _) ->
                match ty with
                  | Te_record _ -> Some path
                  | _ -> None
              ) non_abbrev
            else []
        | _ -> []
      ) ds;
      let mod_name = !St.current_module_name in
      let ns_name = lean_ns_name mod_name in
      let is_library = ns_name <> mod_name in
      (* For library modules, push the top-level namespace so that
         lean_qualified_name returns qualified names (e.g. "Lem_Basic_classes.Eq0"
         instead of bare "Eq0"). Auxiliary files need these qualified opens
         since they don't have the namespace wrapper. *)
      if is_library then
        St.namespace_stack := [ns_name];
      lean_reader_prepass A.env ds;
      lean_ireader_prepass A.env ds;
      lean_cmp_prepass A.env ds;
      lean_fuel_prepass A.env ds;
      lean_supply_prepass A.env ds;
      (* Compute the Inhabited census + tier-2 plans in declaration
         order before emission (defs is fold_right). *)
      lean_inhabited_prepass A.env ds;
      (* Compute the [Inhabited] threading census (failure sites at
         tyvar-typed positions -> signature binders, monotone over the
         call graph) — needs the instance census, so runs after it.
         Also guard-sweeps instance methods (rule 3). *)
      lean_failwith_thread_prepass A.env ds;
      (* The derived-size census for this module's blocks
         (idempotent re-run of the invocation-wide pass). *)
      lean_size_prepass A.env ds;
      let lean_defs = defs false false ds in
      (* Drain any deferred abbrevs (e.g., abbrev mword after class Size).

         INVARIANT: a deferred
         abbrev is for HAND-WRITTEN consumers only. Deferral to end-of-file
         is sound because TYR_subst substitutes the underlying type INLINE
         at every generated use, so nothing in the generated file ever
         references the abbrev by name before it appears. Making generated
         code use the abbrev name would create forward references — do not.

         ORDER: DECLARATION order, deliberately: defs folds
         last-to-first and each abbrev PREPENDS, so the drained list is
         already in declaration order — no rev (the historical `List.rev`
         emitted reverse-declaration order, an accident of a twice-reversed
         cons; single-abbrev files — the only occupied case today — are
         unaffected, byte-compare-verified). *)
      let deferred = Output.flat !St.pending_abbrevs in
      St.pending_abbrevs := [];
      let lean_defs = lean_defs ^ deferred in
      let lean_defs_extra = defs_extra false false ds in
      (* Ensure LemLib.Pervasives is always imported for non-library modules.
         This guarantees the standard namespace opens (Lem_Basic_classes, etc.)
         are available for auto-generated instances even when the source .lem file
         doesn't explicitly import Pervasives (e.g., linux.lem). *)
      if not is_library &&
         not (List.mem "LemLib.Pervasives" !St.collected_imports) then
        St.collected_imports := "LemLib.Pervasives" :: !St.collected_imports;
      (* Imports for target_rep references are collected per-file during rendering:
         - Function CR_simple target reps: via Backend_common.on_cr_simple_applied callback
         - Type TYR_simple target reps: directly in type_def_variant
         This ensures each file only imports modules it actually references. *)
      (* Prepend collected imports (deduplicated, in order) to main body *)
      let imports = List.rev !St.collected_imports in
      let seen = Hashtbl.create 16 in
      let unique_imports = List.filter (fun m ->
        if Hashtbl.mem seen m then false
        else (Hashtbl.add seen m true; true)
      ) imports in
      let imports_output = Output.flat (List.map (fun m ->
        from_string (String.concat "" ["import "; m; "\n"])
      ) unique_imports) in
      let ns_start = if is_library then
        from_string (String.concat "" ["\nnamespace "; ns_name; "\n"])
      else emp in
      let ns_end = if is_library then
        from_string (String.concat "" ["\nend "; ns_name; "\n"])
      else emp in
      (* For non-library modules, open all imported library namespaces so that
         class/type names from transitive dependencies are in scope.
         This is needed because Lean namespaces don't re-export opens.
         We scan the imports collected by THIS file and open the corresponding
         library namespaces. For transitive deps that come through Pervasives,
         we derive all library namespaces from the module environment. *)
      let transitive_opens = if not is_library then begin
        let all_imports = List.rev !St.collected_imports in
        let has_pervasives = List.exists (fun m ->
          m = "LemLib.Pervasives" || m = "LemLib.Pervasives_extra"
        ) all_imports in
        if has_pervasives then
          (* Pervasives imports all core library modules; open their namespaces.
             Also import Pervasives_extra for bridge instances (NumAdd → Add etc.).
             Derive the list of library namespaces from the module environment
             (all modules with a Coq rename are library modules). *)
          let has_pervasives_extra = List.exists (fun m ->
            m = "LemLib.Pervasives_extra"
          ) all_imports in
          let extra_import = if has_pervasives_extra then emp
            else from_string "import LemLib.Pervasives_extra\n" in
          let has_bridges = List.exists (fun m ->
            m = "LemLib.Bridges"
          ) all_imports in
          let bridges_import = if has_bridges then emp
            else from_string "import LemLib.Bridges\n" in
          let lib_namespaces = Types.Pfmap.fold (fun acc _path md ->
            (* the ONE library test (Backend_common.lean_module_is_library) *)
            if Backend_common.lean_module_is_library md then begin
              let mod_name = Path.to_string md.Typed_ast.mod_binding in
              let lean_mod = String.concat "" ["LemLib."; String.capitalize_ascii mod_name] in
              let ns = lean_ns_name lean_mod in
              if List.mem ns acc then acc else ns :: acc
            end else acc
          ) [] A.env.e_env in
          let lib_namespaces = List.rev lib_namespaces in
          Output.flat [extra_import; bridges_import; from_string (open_line lib_namespaces)]
        else
          (* Just open namespaces for direct imports *)
          let ns_list = List.filter_map (fun m ->
            let ns = lean_ns_name m in
            if ns <> m then Some ns else None
          ) all_imports in
          from_string (open_line ns_list)
      end else emp in
      (* Emit open statements for type/class namespaces so auxiliary file
         can reference constructors and class methods unqualified *)
      let opens_output = from_string (open_line !St.auxiliary_opens) in
      (* Fuel-measure obligations (mechanism comment at
         lean_fuel_measure_for): the theorem statements of this module's
         measured functions go into the auxiliary file — lem's home for
         prover-side obligations — behind an import of the hand-written
         proofs module `<Module>_lemMeasureProofs`, which the imports
         above precede (the transitive-open block may itself start with
         imports). Declaration order restored (defs folds last-to-first). *)
      let measure_import, measure_obligations =
        if !St.measure_obligations = [] then emp, emp
        else
          from_string (String.concat "" ["import "; mod_name; "_lemMeasureProofs\n"]),
          Output.flat (
            from_string "\n/- lem: fuel_measure obligations (statements generated here; proofs in the hand-written module imported above) -/\n"
            :: !St.measure_obligations) in
        (* No `compiler.extract_closed false` is emitted (it was, on Lean
           4.28, which evaluated hoisted closed terms when a module LOADED, so
           a closed call to a partial function in an untaken branch
           (`if b then g 10 else 0`) panicked at start-up; generated modules
           then set `compiler.extract_closed false`. From 4.32 closed terms
           are initialised lazily at first use (probe: 4.28 exits 134, 4.32.2
           exits 0), so the option only cost time (+21 % Lean CPU on the
           Cerberus csmith lane) and is no longer emitted. The property is
           guarded by the `lean-untaken-failure` suite target, which fails on
           a toolchain with eager initialisation. *)
        ((to_rope (r"\"") lex_skip need_space @@ imports_output ^ transitive_opens ^ ns_start ^ lean_defs ^ ns_end ^ ws end_lex_skips),
          to_rope (r"\"") lex_skip need_space @@ measure_import ^ transitive_opens ^ opens_output ^ lean_defs_extra ^ measure_obligations ^ ws end_lex_skips)
    ;;
  end
