/-
Third-party provenance (public-readiness M8, 2026-09-24; source notices
checked at Lem 38f87d5fa6b29ec90edfa457faba8a309e32c118).
The Pset and Pmap implementations below are Lean translations of
ocaml-lib/pset.ml and ocaml-lib/pmap.ml, including their AVL algorithms.
They retain the upstream GNU Library General Public License terms in
../LICENSE; the rest of this file follows Lem's BSD-3-Clause default.
The source notices are retained below. This is not a relicensing grant.

From ocaml-lib/pset.ml:
(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* Modified by Scott Owens 2010-10-28 *)


From ocaml-lib/pmap.ml:
(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* Modified by Susmit Sarkar 2010-11-30 *)

-/

/-!
# LemLib — Lean 4 runtime library for Lem

Provides the core types and operations that Lem-generated Lean 4 code depends on:
- `LemOrdering`: three-way comparison type used by set/map operations
- Comparison, arithmetic, and string helpers
- Set and finite-map operations: `Pset`/`Pmap`, translations of Lem's OCaml
  runtime AVL trees (ocaml-lib/pset.ml, pmap.ml). The parity probes and
  LemLibPmapLaws check specific observations and local laws; they are not
  a general correspondence proof. See README.md for the dated validation
  pins and failure/representation limits.

**Convention**: Functions suffixed with `By` take an explicit `(cmp : α → α → LemOrdering)`
comparator. Functions without `By` use Lean's `BEq` or `Ord` type classes.
-/

/- Lem standard library support for Lean 4 -/

/- NO AXIOM AND NO UNSAFE INHABITANT MAY BE INTRODUCED HERE. Two were
   removed and must not come back:
   - an axiom-valued universal inhabitant (`axiom DAEMON : ∀ {α : Type}, α`,
     the value of a legacy `failwith`): logically inconsistent —
     `(DAEMON : Empty)` proves `False`. The backend derives real bounded
     `Inhabited` instances instead and emits `failwithI` (below) with
     `[Inhabited tv]` binders threaded onto the enclosing signatures;
   - an effect-erasure axiom (`runEffectful : (Unit → BaseIO α) → α`, the
     trust boundary of `declare {lean} effectful` target reps): an
     unprovable crossing in every downstream proof cone. Effectful counters
     are threaded as explicit state by the supply lifting (`declare {lean}
     supply val`, `LemLib.supplySplit` below — deterministic,
     kernel-transparent, axiom-free), and the backend refuses that
     declare (deletion record:
     doc/lean-backend/2026-09-01_L2-deletion-record.md).
   Consumers enforce the absence in-build (cerberus-lean
   `scripts/check_theorem_axioms.sh`: a zero-axiom census over the
   hand-written and generated Lean trees plus `#print axioms` probes on
   exemplar cones). -/

/- THE AMBIENT FUEL. `declare {lean}
   fuel val f = `sentinel`` makes `f` a total worker recursing
   structurally on its own counter (`f_lemFuel (lemFuel : Nat) …`); the
   counter STARTS at the ambient fuel, and the ambient fuel is a
   PARAMETER of the generated code: this class, taken as an
   instance-implicit `[LemFuel]` binder by every fuel'd function and by
   every definition that (transitively) reaches one (the backend's fuel
   lifting). The wrapper is `def f [LemFuel] : … := f_lemFuel LemFuel.fuel`,
   so `@f ⟨n⟩ = f_lemFuel n` by rfl, a theorem quantifies `∀ [LemFuel]`
   (or over `n` via `⟨n⟩`), and the executable entry point instantiates it
   once (`letI : LemFuel := ⟨n⟩` at the CLI). NO INSTANCE IS DECLARED
   HERE OR IN ANY GENERATED CODE, by design: [USER 2026-09-03] fuel is an
   execution parameter whose value does not matter, any fuel value can be
   chosen, and every similar magic value is to be removed and replaced
   by a quantified parameter; a global instance would silently give every
   fuel'd function a default, which is exactly the forbidden magic value;
   so would a library default fuel constant, which this file once had
   (tests/comprehensive/check_no_fuel_numerals.sh gates the absence of
   both). -/
class LemFuel where
  fuel : Nat

/- Supply threading ('declare {lean} supply val', the state-passing
   analog of the reader lifting): a DRAW splits the current supply into
   the drawn value and the successor supply. The backend emits
   `let (v, s') := LemLib.supplySplit s` at every draw site of a lifted
   definition. A plain def by design — kernel-transparent (proofs
   unfold it), greppable, no effects anywhere in the mechanism:
   supply threading is deterministic state-passing and introduces no
   nondeterminism or IO. -/
def LemLib.supplySplit (s : Nat) : Nat × Nat := (s, s + 1)

/- Lem uses lowercase 'vector' for its built-in vector type -/
abbrev vector (α : Type) (n : Nat) := Vector α n


/- Ordering type for comparisons -/
inductive LemOrdering where
  | LT : LemOrdering
  | EQ : LemOrdering
  | GT : LemOrdering
  deriving Repr, BEq, Inhabited, DecidableEq

/- Lem's Bool conditional. Generated code writes
   `lem_if c then t else e` for a Lem `if` (whose condition is a `bool`).
   It expands to exactly the kernel term Lean elaborates for a Bool `if`
   (`ite (c = true)` with the `instDecidableEqBool` instance, pinned in
   LemLibTest), but builds it directly: no Bool->Prop coercion search and no
   Decidable instance search, which Lean runs behind `wait_if_type_mvar%`
   and which can get stuck in context (linksem link.lem). The instance's
   arguments are filled by unification, so the condition is written once.
   For a Prop-valued condition (only possible through a target rep that
   produces a Prop) Lean coerces with `decide`: same behaviour, different
   term. -/
syntax (name := lemIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("lem_if " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term
macro_rules
  | `(lem_if $c then $t else $e) => `(@ite _ ($c = true) (instDecidableEqBool _ _) $t $e)

/- Ordering predicates -/
def isLess (o : LemOrdering) : Bool := o == .LT
def isLessEqual (o : LemOrdering) : Bool := o != .GT
def isGreater (o : LemOrdering) : Bool := o == .GT
def isGreaterEqual (o : LemOrdering) : Bool := o != .LT

/- Inhabited for Sum (not in Lean core; needed by ground-typed failwithI
   sites at sum types). Left-biased, right as fallback. -/
instance [Inhabited α] : Inhabited (α ⊕ β) := ⟨.inl default⟩
instance (priority := low) [Inhabited β] : Inhabited (α ⊕ β) := ⟨.inr default⟩

/- BEq/Ord for Sum (neither is in Lean core). Unblocks `deriving BEq,
   Ord` on generated types with either-typed constructor fields.
   OCaml-polymorphic-comparison parity: lem `either 'a 'b = Left of 'a
   | Right of 'b` (library/either.lem:16) renders on the OCaml backend
   as `Either.either` (either.lem:20), i.e. OCaml's
   `type ('a,'b) t = Left of 'a | Right of 'b`: both constructors are blocks
   with tags in declaration order (Left = 0, Right = 1). OCaml (=) is
   structural per constructor; OCaml compare orders by tag first, then
   fields left-to-right (runtime/compare.c: tag comparison precedes
   field walk). Mirror: inl/Left < inr/Right, payload comparison within
   the same constructor, structural equality across. -/
instance [BEq α] [BEq β] : BEq (α ⊕ β) where
  beq
    | .inl a, .inl b => a == b
    | .inr a, .inr b => a == b
    | _, _ => false

instance [Ord α] [Ord β] : Ord (α ⊕ β) where
  compare
    | .inl a, .inl b => compare a b
    | .inl _, .inr _ => .lt
    | .inr _, .inl _ => .gt
    | .inr a, .inr b => compare a b

/- Ord for Unit (not in Lean stdlib, needed by generated code) -/
instance : Ord Unit where compare _ _ := .eq

/- Ord for LemOrdering: Lem programs build sets of
   comparison results (`Set.member (compare a b) {LT; EQ}`), which needs
   `SetType ordering`, derived from `Ord`. The order is the OCaml target's:
   `ordering` is `int` there with LT = -1, EQ = 0, GT = 1, so LT < EQ < GT. -/
instance : Ord LemOrdering where
  compare a b :=
    let rank : LemOrdering → Nat := fun | .LT => 0 | .EQ => 1 | .GT => 2
    compare (rank a) (rank b)

/- Ord instance for Prod (not in Lean stdlib) -/
instance [Ord α] [Ord β] : Ord (α × β) where
  compare p q :=
    match compare p.1 q.1 with
    | .lt => .lt
    | .gt => .gt
    | .eq => compare p.2 q.2

/- Default comparison via Ord -/
def defaultCompare [Ord α] (x y : α) : LemOrdering :=
  match compare x y with
  | .lt => .LT
  | .eq => .EQ
  | .gt => .GT

def defaultLess [Ord α] (x y : α) : Bool := isLess (defaultCompare x y)
def defaultLessEq [Ord α] (x y : α) : Bool := isLessEqual (defaultCompare x y)
def defaultGreater [Ord α] (x y : α) : Bool := isGreater (defaultCompare x y)
def defaultGreaterEq [Ord α] (x y : α) : Bool := isGreaterEqual (defaultCompare x y)

/- failwithI: failure at a KNOWN-INHABITED type. The Lean
   backend emits this instead of failwith at call sites whose result type
   is syntactically GROUND (no type variables), where instance resolution
   cannot require constraint propagation. Properties, each load-bearing:
   - opaque: NO equations — an error branch is not provably equal to any
     value (strictly stronger claim hygiene than a `:= default` body);
   - axiom-free: the `:= default` initializer only witnesses
     inhabitation; opaque does not expose it definitionally;
   - computable at runtime via @[implemented_by]: panics with the
     message. -/
/- `never_extract` on the IMPLEMENTATION too: the compiler substitutes the
   `implemented_by` target before closed-term extraction, so an attribute
   on the opaque alone does not protect `failwithIImpl "msg"` at a closed
   type from being lifted to module initialisation (measured: `import
   LemLib` alone aborted under LEAN_ABORT_ON_PANIC=1 until this). -/
@[never_extract] private unsafe def failwithIImpl {α : Type} [Inhabited α] (msg : String) : α :=
  panic! msg
/- `never_extract`: a closed application `failwithI "msg"` at a closed
   type is otherwise lifted by the compiler's closed-term extraction into
   a module-initialisation constant, so the panic fired at INIT of every
   importing binary under LEAN_ABORT_ON_PANIC=1 instead of at the failing
   program point — which is where the OCaml reference raises. That is the
   4.28–4.32 behaviour; Lean 4.35.0 initialises extracted closed terms
   lazily (a `lean_once_cell_t`, at first use), so on 4.35.0 what the
   attribute buys is "once per SITE, not once per process": without it a
   reached closed failure would be cached after its first evaluation and a
   second reach would be silent. The attribute is necessary on both
   (doc/lean-backend/2026-10-21_lean-4.35-record.md §3 (d); the suite's
   `lean-untaken-failure` leg 4 guards it). -/
@[implemented_by failwithIImpl, never_extract]
opaque failwithI {α : Type} [Inhabited α] (msg : String) : α := default

/- Fail-stop for executables ([USER 2026-09-30] agreed D1). A reached
   `failwithI` is a Lean `panic!`:
   unless the runtime aborts, it prints the message and CONTINUES with the
   `Inhabited` default ("library-call semantics"), so a program whose model
   fails could exit 0 with plausible-looking output where the OCaml target
   raises and stops. An executable over generated code calls
   `lemRequireAbortOnPanic` first thing in `main`: it REFUSES to run (an
   attributed message on stderr, exit 2) unless `LEAN_ABORT_ON_PANIC` is
   exactly `1`, so every reached failure is a fail-stop. No extern and no
   unsafe code (an extern that set the runtime's exit-on-panic flag was
   removed by that ruling). The pattern is Cerberus's driver refusal
   (lean_frontend/Main.lean), which measured that the runtime aborts when
   the variable is merely PRESENT ("1", "0" and "" all abort); this check is
   stricter (the value must be `1`). -/
def lemRequireAbortOnPanic : IO Unit := do
  match ← IO.getEnv "LEAN_ABORT_ON_PANIC" with
  | some "1" => pure ()
  | none =>
    IO.eprintln "LemLib lemRequireAbortOnPanic: refused — LEAN_ABORT_ON_PANIC is not set: a reached failure (a Lean panic!) would print and then CONTINUE with a default value where the OCaml target stops; run with LEAN_ABORT_ON_PANIC=1"
    IO.Process.exit 2
  | some x =>
    IO.eprintln ("LemLib lemRequireAbortOnPanic: refused — LEAN_ABORT_ON_PANIC is \"" ++ x ++
      "\", not 1: the Lean runtime aborts on a panic whenever the variable is set, but this check requires exactly 1 so the fail-stop contract has one spelling; run with LEAN_ABORT_ON_PANIC=1")
    IO.Process.exit 2

/- Sequencing: Lem's `let _ = e1 in e2` evaluates e1 for its
   effect (a diagnostic, or a failure that must stop the program, as the
   OCaml exception does). Lean's compiler drops unused pure values and treats
   every Unit value as `()`, so the backend emits
   `lemSeq (fun _ => e1) (fun _ => e2)`. Logically `e2`; the runtime
   implementation forces `e1` first by storing its value in a fresh IO
   reference: a `BaseIO` effect the compiler must keep. (A pure "use" is not
   enough: an `if ptrAddrUnsafe x == 1 then b () else b ()` was simplified
   away, and arity reduction then dropped `a` altogether.)
   BOUNDARY ([USER 2026-09-30] agreed D1): `lemSeqImpl` is on the
   native-seam boundary list as TEMPORARY. Kernel-vs-runtime gap: `lemSeq`
   is a transparent def, logically `b ()`; at run time it also forces `a`.
   It is an exception, by that ruling, to the no-unsafe-effect-projection
   note at the top of this file. Named mover: the failure-monad
   translation (doc/lean-backend/TODO.md item 24), which makes strictness
   part of the semantics and deletes this seam. -/
@[never_extract, noinline] private unsafe def lemSeqImpl {α β : Type} (a : Unit → α) (b : Unit → β) : β :=
  match unsafeBaseIO (do
      let r ← IO.mkRef (none : Option α)
      r.set (some (a ()))
      pure (b ())) with
  | v => v
@[implemented_by lemSeqImpl] def lemSeq {α β : Type} (_ : Unit → α) (b : Unit → β) : β := b ()

/- Comparing function values. OCaml's polymorphic compare
   and structural equality raise `Invalid_argument "compare: functional
   value"` when they REACH a closure, and only then (`GOT [] = GOT []`
   is fine). Backend-derived structural comparisons of types with
   function-typed fields call these at the function-typed positions, so a
   comparison fails whenever it reaches a closure: exactly OCaml's `=`, but
   NOT OCaml's `compare`, which returns 0 for the same closure object
   (physical equality). That is an open discrepancy awaiting a ruling
   (TODO item 32; parity probe p_fn_compare_same_closure). -/
@[never_extract] def lemFunctionalCompare {α β : Type} (_ _ : α → β) : Ordering :=
  failwithI "compare: functional value"
@[never_extract] def lemFunctionalBeq {α β : Type} (_ _ : α → β) : Bool :=
  failwithI "compare: functional value"

/- fuelExhaustedWith: out-of-fuel sentinel for fuel'd defs whose return
   type is pure (no error channel) and possibly polymorphic.
   The witness — any in-scope value of the return type, typically one of
   the worker's own arguments — discharges inhabitation LOCALLY: no
   [Inhabited] constraint propagates into generated signatures, and no
   generated-instance fallback enters the cone. Same load-bearing properties as failwithI: opaque (no
   equations — the fuel-exhausted branch is not provably equal to
   anything, in particular NOT to the witness), axiom-free, and loud at
   runtime via @[implemented_by] panic. -/
@[never_extract] private unsafe def fuelExhaustedWithImpl {α : Type} (msg : String) (witness : α) : α :=
  @panic α ⟨witness⟩ msg
@[implemented_by fuelExhaustedWithImpl, never_extract]
opaque fuelExhaustedWith {α : Type} (msg : String) (witness : α) : α := witness

/- Vector slice — lem `vector` slicing:
   * WIDTH-FROM-RETURN-TYPE: the result length is the implicit `m`
     inferred from the USE SITE's expected type — the same convention as
     mwordExtract/mwordConcat below ("hi is redundant", Isabelle
     Word.slice); the `_stop` argument is therefore IGNORED by design
     (redundant with `m`), and is named `_stop` to say so.
   * OUT-OF-RANGE FAILS LOUDLY:
     the OCaml rep `vector_slice n1 n2 (Vector a) = Vector (Array.sub a n1 n2)`
     (ocaml-lib/vector.ml:33) raises Invalid_argument when the slice is
     not within the array; the previous pad-with-default arm SUCCEEDED
     there. lem's typechecker relates m/start/stop, so the arm is
     unreachable from type-correct generated code on both targets.
   * Injected into the core `Vector` namespace so generated projections
     `v.slice` resolve (a LemLib-local name would need backend
     qualification). -/
namespace Vector
def slice [Inhabited α] {n m : Nat} (v : Vector α n) (start _stop : Nat) : Vector α m :=
  if start + m > n then failwithI "Invalid_argument \"Array.sub\""
  else Vector.ofFn fun i => (v.toArray.extract start (start + m)).getD i.val default
end Vector

/- Message-less variant for 'declare {lean} fuel val' sentinels: the lem
   backtick lexer excludes double quotes, so declares cannot carry a
   message string. Unfolds to the opaque core.
   `never_extract`: without it the
   compiler lifts a CLOSED application `fuelExhausted w` to a module-init
   constant and evaluates the sentinel eagerly (silently, panic messages
   are suppressed during initialisation), so a sufficient-fuel run could
   abort on the sentinel it never reached. Regression: the strict native
   parity probe `tests/comprehensive/parity` `p_lem_size` under
   LEAN_ABORT_ON_PANIC=1. On Lean 4.35.0 extraction is lazy (a once-cell at
   first use), so the eager-abort failure mode is gone there and the
   attribute's purpose becomes once-per-site rather than once-per-process
   (see `failwithI` above); it stays. -/
@[never_extract] def fuelExhausted {α : Type} (witness : α) : α :=
  fuelExhaustedWith "lem: fuel exhausted" witness

/- fromJustI: ground-site head for msg-carrying fromJust helpers
   (declare {lean} ground_rep, e.g. cerberus Utils.fromJust). A REAL def:
   the success equation `fromJustI msg (some x) = x` holds by rfl
   (theorems over lookups keep proving); only the failure leaf is opaque
   (failwithI), keeping the cone axiom-free.
   fromJustI1: the msg-less variant (Maybe_extra.fromJust). -/
def fromJustI {α : Type} [Inhabited α] (msg : String) : Option α → α
  | some x => x
  | none => failwithI msg

def fromJustI1 {α : Type} [Inhabited α] : Option α → α
  | some x => x
  | none => failwithI "fromJust"


/- List operations -/
def listEqualBy (eq : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | x :: xs, y :: ys => eq x y && listEqualBy eq xs ys
  | _, _ => false

def listMemberBy (eq : α → α → Bool) (x : α) : List α → Bool
  | [] => false
  | y :: ys => eq x y || listMemberBy eq x ys

/- Tuple equality -/
def tupleEqualBy (eq1 : α → α → Bool) (eq2 : β → β → Bool) (p1 : α × β) (p2 : α × β) : Bool :=
  eq1 p1.1 p2.1 && eq2 p1.2 p2.2

/- Natural number operations -/
@[inline] def natPower (base exp : Nat) : Nat := base ^ exp
@[inline] def natMin (a b : Nat) : Nat := min a b
@[inline] def natMax (a b : Nat) : Nat := max a b
@[inline] def natLtb (a b : Nat) : Bool := a < b
@[inline] def natLteb (a b : Nat) : Bool := a ≤ b
@[inline] def natGtb (a b : Nat) : Bool := a > b
@[inline] def natGteb (a b : Nat) : Bool := a ≥ b

/- Exponentiation by squaring -/
def gen_pow_aux (mul : α → α → α) (one : α) (base : α) (exp : Nat) : α :=
  match exp with
  | 0 => one
  | 1 => mul one base
  | n + 2 =>
    let half := (n + 2) / 2
    let one' := if (n + 2) % 2 == 0 then one else mul one base
    gen_pow_aux mul one' (mul base base) half
termination_by exp
decreasing_by omega

/- Integer operations -/
@[inline] def intLtb (a b : Int) : Bool := a < b
@[inline] def intLteb (a b : Int) : Bool := a ≤ b
@[inline] def intGtb (a b : Int) : Bool := a > b
@[inline] def intGteb (a b : Int) : Bool := a ≥ b

/- String operations -/
def stringMakeString (n : Nat) (c : Char) : String := String.ofList (List.replicate n c)

/- Sorting by LemOrdering comparison -/
def sort_by_ordering (cmp : α → α → LemOrdering) (l : List α) : List α :=
  let leanCmp : α → α → Bool := fun a b => match cmp a b with
    | .LT => true
    | .EQ => true
    | .GT => false
  l.mergeSort leanCmp

/- ============================================================================
   Sets and finite maps: Lean translations of Lem's OCaml runtime
   (ocaml-lib/pset.ml, modified by Scott Owens 2010-10-28;
   ocaml-lib/pmap.ml, modified by Susmit Sarkar 2010-11-30).
   Source notices are at the top of this file.
   ============================================================================

   [USER 2026-09-03] ruling: the OCaml target is the reference semantics
   of a lem program and there are to be ZERO behavioural discrepancies.
   An earlier Lean representation (a comparator-keyed insertion-order
   list for sets; a `Std.TreeMap`-indexed, insertion-sequenced `Fmap`)
   did not reproduce the OCaml observables: iteration/fold/toList order
   (OCaml: ascending by comparator), Pmap.add replacing the key AND value
   of a comparator-equal binding, Pmap.equal comparing keys with the
   map's comparator, Set.choose_and_split / set_case / union
   representatives, and every
   panic-order nuance of for_all/exists. Rather than approximate them
   one by one, the two AVL modules follow the source algorithms. Tree
   shape affects observables: which representative of comparator-equal
   but distinguishable elements a `union` keeps depends on subtree
   HEIGHTS in pset.ml. Each function cites its OCaml source line. This
   translation and the finite parity probes are evidence, not a theorem
   about every operation sequence. Comparators are lem's `LemOrdering`; `c = 0`,
   `c < 0`, `c > 0` in the OCaml read `.EQ`, `.LT`, `.GT`.

   Failure parity: where the OCaml raises (Not_found on choose/min_elt of
   the empty set, Invalid_argument in bal/remove_min_elt on ill-formed
   input) the port uses failwithI (exception class (a)). Native execution
   must set LEAN_ABORT_ON_PANIC=1 to abort on a reached panic. Lean may
   erase unused pure failures; general strict-failure parity is not proved.

   Termination: structural where the OCaml is structural on one tree.
   The functions whose OCaml recursion is not structural on one argument
   (`join`; union/inter/diff/subset on two trees via `split`; merge on
   two maps; compare/equal on two enumerations; the closure loop of `tc`)
   are STRUCTURAL RECURSIONS ON A DATA MEASURE — an index computed from
   the arguments that bounds the recursion exactly: the stored AVL
   heights (`height s1 + height s2 + 1`: each level strictly decreases
   the sum; split never increases a height), the element counts, the
   finite square of a relation's endpoints. This is the admissible third
   form of the no-magic-values rule ([USER 2026-09-03]: the rule's aim is to
   forbid values that limit the semantics or limit the ways a customer
   can reason about the semantics): nothing is chosen, the kernel
   unfolds it (unlike well-founded recursion, which blocks closed-term
   `rfl`/`decide` — `join` was moved off WF recursion for exactly that
   reason), and the exhaustion arm —
   unreachable on well-formed input — is the loud `fuelExhaustedWith`
   sentinel, never a silent truncation. The one CALLER-FUELLED primitive
   is `lfpGo` (option (a): its caller `tc` supplies the data measure).

   Two-target pins: tests/comprehensive/parity/probes/p_set_ops.lem,
   p_map_ops.lem, p_map_beq.lem, p_cmp_order.lem, p_show.lem. -/

/-- pset.ml:16 `type 'a rep = Empty | Node of 'a rep * 'a * 'a rep * int`.
    The lem `set 'a` Lean representation (library/set.lem). `Empty` is
    the first, nullary constructor: `lean_box(0)` is a valid empty set. -/
inductive Pset (α : Type) : Type where
  | Empty : Pset α
  | Node : Pset α → α → Pset α → Nat → Pset α

instance : Inhabited (Pset α) := ⟨.Empty⟩

namespace Pset
variable {α β : Type}

/-- pset.ml:21 -/
def height : Pset α → Nat
  | Empty => 0
  | Node _ _ _ h => h

/-- pset.ml:28 -/
def create (l : Pset α) (v : α) (r : Pset α) : Pset α :=
  let hl := height l
  let hr := height r
  Node l v r (if hl >= hr then hl + 1 else hr + 1)

/-- pset.ml:37 `bal` — one rebalancing step; `invalid_arg "Set.bal"` on
    the (unreachable by construction) ill-formed shapes. -/
def bal (l : Pset α) (v : α) (r : Pset α) : Pset α :=
  let hl := height l
  let hr := height r
  if hl > hr + 2 then
    match l with
    | Empty => failwithI "Set.bal"
    | Node ll lv lr _ =>
      if height ll >= height lr then create ll lv (create lr v r)
      else match lr with
        | Empty => failwithI "Set.bal"
        | Node lrl lrv lrr _ => create (create ll lv lrl) lrv (create lrr v r)
  else if hr > hl + 2 then
    match r with
    | Empty => failwithI "Set.bal"
    | Node rl rv rr _ =>
      if height rr >= height rl then create (create l v rl) rv rr
      else match rl with
        | Empty => failwithI "Set.bal"
        | Node rll rlv rlr _ => create (create l v rll) rlv (create rlr rv rr)
  else Node l v r (if hl >= hr then hl + 1 else hr + 1)

/-- pset.ml:76 `add` — a comparator-EQ element already present wins (the
    set is returned unchanged). -/
def add (cmp : α → α → LemOrdering) (x : α) : Pset α → Pset α
  | Empty => Node Empty x Empty 1
  | Node l v r h =>
    match cmp x v with
    | .EQ => Node l v r h
    | .LT => bal (add cmp x l) v r
    | .GT => bal l v (add cmp x r)

/-- Heights consistent with the shape (`h = max hl hr + 1` at every node):
    the part of the AVL invariant the height-indexed recursions below
    rely on for their index to be exact. Computable (`Bool`), so a proof
    can `decide` it on a closed tree; the well-formedness predicate the
    Pmap laws (LemLibPmapLaws) build on. -/
def heightsOk : Pset α → Bool
  | Empty => true
  | Node l _ r h =>
    let hl := height l
    let hr := height r
    h == (if hl >= hr then hl + 1 else hr + 1) && heightsOk l && heightsOk r

/-- pset.ml:86 `join` — STRUCTURAL recursion on the DATA MEASURE
    `height l + height r + 1` (the recursion descends into a child of the
    taller side, whose stored height is smaller when heights are
    consistent). Well-founded recursion on `sizeOf l + sizeOf r`, which
    this was, is what the kernel cannot unfold — every closed-term
    `rfl`/`decide` through `union`/`remove`/`fmapUnionBy` stopped here (a
    consumer measured 17 broken proofs). The
    index is not a chosen value ([USER 2026-09-03] third form: "nothing is
    chosen, nothing bounds the semantics, a proof can unfold it"); its
    exhaustion arm is unreachable on heights-consistent trees and LOUD
    otherwise. `LemLibTheorems.PsetJoin.join_eq` proves it equal to the
    well-founded definition under `heightsOk`. -/
def joinGo (cmp : α → α → LemOrdering) : Nat → Pset α → α → Pset α → Pset α
  | 0, l, _, _ => fuelExhaustedWith "Pset.join: height index exhausted (unreachable: AVL heights bound the recursion)" l
  | h + 1, l, v, r =>
    match l, r with
    | Empty, _ => add cmp v r
    | _, Empty => add cmp v l
    | Node ll lv lr lh, Node rl rv rr rh =>
      if lh > rh + 2 then bal ll lv (joinGo cmp h lr v (Node rl rv rr rh))
      else if rh > lh + 2 then bal (joinGo cmp h (Node ll lv lr lh) v rl) rv rr
      else create l v r

def join (cmp : α → α → LemOrdering) (l : Pset α) (v : α) (r : Pset α) : Pset α :=
  joinGo cmp (height l + height r + 1) l v r

/-- pset.ml:97 `min_elt` (raises Not_found on Empty — the callers decide:
    `choose` fails loudly, `min_elt_opt` yields none). -/
def minElt? : Pset α → Option α
  | Empty => none
  | Node Empty v _ _ => some v
  | Node l _ _ _ => minElt? l

/-- pset.ml:102 `max_elt` -/
def maxElt? : Pset α → Option α
  | Empty => none
  | Node _ v Empty _ => some v
  | Node _ _ r _ => maxElt? r

/-- pset.ml:109 `remove_min_elt` -/
def removeMinElt : Pset α → Pset α
  | Empty => failwithI "Set.remove_min_elt"
  | Node Empty _ r _ => r
  | Node l v r _ => bal (removeMinElt l) v r

/-- pset.ml:117 `merge` (all elements of t1 precede those of t2) -/
def merge (t1 t2 : Pset α) : Pset α :=
  match t1, t2 with
  | Empty, t => t
  | t, Empty => t
  | _, _ =>
    match minElt? t2 with
    | some m => bal t1 m (removeMinElt t2)
    | none => failwithI "Set.merge: unreachable (non-empty tree without a minimum)"

/-- pset.ml:126 `concat` -/
def concat (cmp : α → α → LemOrdering) (t1 t2 : Pset α) : Pset α :=
  match t1, t2 with
  | Empty, t => t
  | t, Empty => t
  | _, _ =>
    match minElt? t2 with
    | some m => join cmp t1 m (removeMinElt t2)
    | none => failwithI "Set.concat: unreachable (non-empty tree without a minimum)"

/-- pset.ml:137 `split x s = (l, present, r)` -/
def split (cmp : α → α → LemOrdering) (x : α) : Pset α → Pset α × Bool × Pset α
  | Empty => (Empty, false, Empty)
  | Node l v r _ =>
    match cmp x v with
    | .EQ => (l, true, r)
    | .LT => let (ll, pres, rl) := split cmp x l; (ll, pres, join cmp rl v r)
    | .GT => let (lr, pres, rr) := split cmp x r; (join cmp l v lr, pres, rr)

/-- pset.ml:151 -/
def isEmpty : Pset α → Bool
  | Empty => true
  | _ => false

/-- pset.ml:153 `mem` -/
def mem (cmp : α → α → LemOrdering) (x : α) : Pset α → Bool
  | Empty => false
  | Node l v r _ =>
    match cmp x v with
    | .EQ => true
    | .LT => mem cmp x l
    | .GT => mem cmp x r

/-- pset.ml:159 -/
def singleton (x : α) : Pset α := Node Empty x Empty 1

/-- pset.ml:161 `remove` -/
def remove (cmp : α → α → LemOrdering) (x : α) : Pset α → Pset α
  | Empty => Empty
  | Node l v r _ =>
    match cmp x v with
    | .EQ => merge l r
    | .LT => bal (remove cmp x l) v r
    | .GT => bal l v (remove cmp x r)

/-- pset.ml:168 `union` — height-fuelled (see the header). `h2 = 1` /
    `h1 = 1` are the OCaml's singleton short-cuts and decide WHICH
    representative of a comparator-equal pair survives. -/
def unionGo (cmp : α → α → LemOrdering) : Nat → Pset α → Pset α → Pset α
  | 0, s1, _ => fuelExhaustedWith "Pset.union: height fuel exhausted (unreachable: AVL heights bound the recursion)" s1
  | fuel + 1, s1, s2 =>
    match s1, s2 with
    | Empty, t2 => t2
    | t1, Empty => t1
    | Node l1 v1 r1 h1, Node l2 v2 r2 h2 =>
      if h1 >= h2 then
        if h2 == 1 then add cmp v2 s1
        else
          let (l2', _, r2') := split cmp v1 s2
          join cmp (unionGo cmp fuel l1 l2') v1 (unionGo cmp fuel r1 r2')
      else
        if h1 == 1 then add cmp v1 s2
        else
          let (l1', _, r1') := split cmp v2 s1
          join cmp (unionGo cmp fuel l1' l2) v2 (unionGo cmp fuel r1' r2)

def union (cmp : α → α → LemOrdering) (s1 s2 : Pset α) : Pset α :=
  unionGo cmp (height s1 + height s2 + 1) s1 s2

/-- pset.ml:184 `inter` (keeps s1's representative) -/
def interGo (cmp : α → α → LemOrdering) : Nat → Pset α → Pset α → Pset α
  | 0, s1, _ => fuelExhaustedWith "Pset.inter: height fuel exhausted (unreachable)" s1
  | fuel + 1, s1, s2 =>
    match s1, s2 with
    | Empty, _ => Empty
    | _, Empty => Empty
    | Node l1 v1 r1 _, t2 =>
      match split cmp v1 t2 with
      | (l2, false, r2) => concat cmp (interGo cmp fuel l1 l2) (interGo cmp fuel r1 r2)
      | (l2, true, r2) => join cmp (interGo cmp fuel l1 l2) v1 (interGo cmp fuel r1 r2)

def inter (cmp : α → α → LemOrdering) (s1 s2 : Pset α) : Pset α :=
  interGo cmp (height s1 + height s2 + 1) s1 s2

/-- pset.ml:194 `diff` -/
def diffGo (cmp : α → α → LemOrdering) : Nat → Pset α → Pset α → Pset α
  | 0, s1, _ => fuelExhaustedWith "Pset.diff: height fuel exhausted (unreachable)" s1
  | fuel + 1, s1, s2 =>
    match s1, s2 with
    | Empty, _ => Empty
    | t1, Empty => t1
    | Node l1 v1 r1 _, t2 =>
      match split cmp v1 t2 with
      | (l2, false, r2) => join cmp (diffGo cmp fuel l1 l2) v1 (diffGo cmp fuel r1 r2)
      | (l2, true, r2) => concat cmp (diffGo cmp fuel l1 l2) (diffGo cmp fuel r1 r2)

def diff (cmp : α → α → LemOrdering) (s1 s2 : Pset α) : Pset α :=
  diffGo cmp (height s1 + height s2 + 1) s1 s2

/-- pset.ml:204 `type 'a enumeration = End | More of 'a * 'a rep * 'a enumeration` -/
inductive Enum (α : Type) : Type where
  | End : Enum α
  | More : α → Pset α → Enum α → Enum α

/-- pset.ml:213 `cons_enum` -/
def consEnum : Pset α → Enum α → Enum α
  | Empty, e => e
  | Node l v r _, e => consEnum l (.More v r e)

/-- pset.ml:204 `cardinal` -/
def cardinal : Pset α → Nat
  | Empty => 0
  | Node l _ r _ => cardinal l + 1 + cardinal r

/-- pset.ml:218 `compare_aux` — one element consumed per step, so the
    element counts bound the recursion. -/
def compareAux (cmp : α → α → LemOrdering) : Nat → Enum α → Enum α → LemOrdering
  | 0, _, _ => fuelExhaustedWith "Pset.compare: fuel exhausted (unreachable: bounded by the element counts)" .EQ
  | fuel + 1, e1, e2 =>
    match e1, e2 with
    | .End, .End => .EQ
    | .End, _ => .LT
    | _, .End => .GT
    | .More v1 r1 e1, .More v2 r2 e2 =>
      match cmp v1 v2 with
      | .EQ => compareAux cmp fuel (consEnum r1 e1) (consEnum r2 e2)
      | c => c

/-- pset.ml:229 `compare` -/
def compare (cmp : α → α → LemOrdering) (s1 s2 : Pset α) : LemOrdering :=
  compareAux cmp (cardinal s1 + cardinal s2 + 1) (consEnum s1 .End) (consEnum s2 .End)

/-- pset.ml:232 `equal` -/
def equal (cmp : α → α → LemOrdering) (s1 s2 : Pset α) : Bool :=
  match compare cmp s1 s2 with
  | .EQ => true
  | _ => false

/-- pset.ml:235 `subset` (height-fuelled; the synthetic `Node (l1, v1,
    Empty, 0)` of the OCaml is reproduced literally) -/
def subsetGo (cmp : α → α → LemOrdering) : Nat → Pset α → Pset α → Bool
  | 0, _, _ => fuelExhaustedWith "Pset.subset: height fuel exhausted (unreachable)" false
  | fuel + 1, s1, s2 =>
    match s1, s2 with
    | Empty, _ => true
    | _, Empty => false
    | Node l1 v1 r1 _, Node l2 v2 r2 h2 =>
      match cmp v1 v2 with
      | .EQ => subsetGo cmp fuel l1 l2 && subsetGo cmp fuel r1 r2
      | .LT => subsetGo cmp fuel (Node l1 v1 Empty 0) l2 && subsetGo cmp fuel r1 (Node l2 v2 r2 h2)
      | .GT => subsetGo cmp fuel (Node Empty v1 r1 0) r2 && subsetGo cmp fuel l1 (Node l2 v2 r2 h2)

def subset (cmp : α → α → LemOrdering) (s1 s2 : Pset α) : Bool :=
  subsetGo cmp (height s1 + height s2 + 1) s1 s2

/-- pset.ml:254 `fold` — in-order (ascending): `fold f r (f v (fold f l accu))` -/
def fold (f : α → β → β) : Pset α → β → β
  | Empty, accu => accu
  | Node l v r _, accu => fold f r (f v (fold f l accu))

/-- pset.ml:259 `map` -/
def map (cmp : β → β → LemOrdering) (f : α → β) (s : Pset α) : Pset β :=
  fold (fun e s => add cmp (f e) s) s Empty

/-- pset.ml:261 `map_union` -/
def mapUnion (cmp : β → β → LemOrdering) (f : α → Pset β) (s : Pset α) : Pset β :=
  fold (fun e s => union cmp (f e) s) s Empty

/-- pset.ml:263 `for_all` — `p v && for_all p l && for_all p r` (this
    exact order decides which element a failing `p` fails on) -/
def forAll (p : α → Bool) : Pset α → Bool
  | Empty => true
  | Node l v r _ => p v && forAll p l && forAll p r

/-- pset.ml:267 `exists` -/
def exists_ (p : α → Bool) : Pset α → Bool
  | Empty => false
  | Node l v r _ => p v || exists_ p l || exists_ p r

/-- pset.ml:271 `filter` (root, then left, then right, accumulating with `add`) -/
def filterAux (cmp : α → α → LemOrdering) (p : α → Bool) : Pset α → Pset α → Pset α
  | accu, Empty => accu
  | accu, Node l v r _ => filterAux cmp p (filterAux cmp p (if p v then add cmp v accu else accu) l) r

def filter (cmp : α → α → LemOrdering) (p : α → Bool) (s : Pset α) : Pset α :=
  filterAux cmp p Empty s

/-- pset.ml:278 `partition` -/
def partitionAux (cmp : α → α → LemOrdering) (p : α → Bool) : Pset α × Pset α → Pset α → Pset α × Pset α
  | accu, Empty => accu
  | (t, f), Node l v r _ =>
    partitionAux cmp p (partitionAux cmp p (if p v then (add cmp v t, f) else (t, add cmp v f)) l) r

def partition (cmp : α → α → LemOrdering) (p : α → Bool) (s : Pset α) : Pset α × Pset α :=
  partitionAux cmp p (Empty, Empty) s

/-- pset.ml:290 `elements` — ascending -/
def elementsAux : List α → Pset α → List α
  | accu, Empty => accu
  | accu, Node l v r _ => elementsAux (v :: elementsAux accu r) l

def elements (s : Pset α) : List α := elementsAux [] s

/-- pset.ml:297 `choose = min_elt` (Not_found on the empty set) -/
def choose [Inhabited α] (s : Pset α) : α :=
  match minElt? s with
  | some v => v
  | none => failwithI "Not_found (Pset.choose of the empty set)"

/-- pset.ml:367 `from_list c l = List.fold_left (fun s x -> add x s) (empty c) l`
    — the FIRST of several comparator-equal list elements survives -/
def fromList (cmp : α → α → LemOrdering) (l : List α) : Pset α :=
  l.foldl (fun s x => add cmp x s) Empty

/-- pset.ml:480 `bigunion c xss = fold union xss (empty c)` (note the
    argument order of `union`: the element set is s1, the accumulator s2) -/
def bigunion (cmp : α → α → LemOrdering) (xss : Pset (Pset α)) : Pset α :=
  fold (fun s acc => union cmp s acc) xss Empty

/-- pset.ml:483 `sigma` -/
def sigma (cmp : (α × β) → (α × β) → LemOrdering) (xs : Pset α) (ys : α → Pset β) : Pset (α × β) :=
  fold (fun x xys => fold (fun y xys => add cmp (x, y) xys) (ys x) xys) xs Empty

/-- pset.ml:486 `cross` -/
def cross (cmp : (α × β) → (α × β) → LemOrdering) (xs : Pset α) (ys : Pset β) : Pset (α × β) :=
  sigma cmp xs (fun _ => ys)

/-- pset.ml:488 `lfp s f = let s' = f s in if subset s' s then s else lfp (union s' s) f`
    — the OCaml may loop forever for an arbitrary `f`; the port is the
    CALLER-FUELLED primitive (option (a) of the fuel-parameter design
    note): its one caller, `tc` below, supplies a data measure; at zero
    it fails LOUDLY (never a value that looks like a result). -/
def lfpGo (cmp : α → α → LemOrdering) (f : Pset α → Pset α) : Nat → Pset α → Pset α
  | 0, s => fuelExhaustedWith "Pset.lfp: fuel exhausted" s
  | fuel + 1, s =>
    let s' := f s
    if subset cmp s' s then s else lfpGo cmp f fuel (union cmp s' s)

/-- pset.ml:494 `tc` — transitive closure of a relation given as a set of
    pairs; `one_step` adds (x,z) for every (x,y),(y',z) with y ~ y' under
    the pair comparator's diagonal. The OCaml iterates `lfp` with no
    bound. Here the iteration count is a DATA MEASURE, not a chosen value:
    every productive step adds at least one pair drawn from the finite
    square of r's endpoints (at most (2|r|)^2 of them), so the closure is
    reached within (2|r|)^2 + 1 steps for any comparator that is a total
    preorder (every generated comparator is); the form is the admissible
    third form of the no-magic-values rule ([USER 2026-09-03]: the rule's aim
    is to forbid values that limit the semantics or limit the ways a
    customer can reason about the semantics — nothing is chosen here and a
    proof can unfold it), the same form as the height-indexed set/map
    recursions above. On an ill-behaved comparator the OCaml loops; the
    port's `lfpGo` exhausts LOUDLY instead (the accepted direction).
    The alternative — a caller-fuelled `tc` via `{lean} fuel_consumer` on
    `Relation.transitiveClosureByCmp` — was built and withdrawn: it puts a
    `[LemFuel]` binder on every relation function for no semantic reason
    and edits the library source. Whether this bound counts as a data
    measure is TODO item 41. -/
def tc (cmp : (α × α) → (α × α) → LemOrdering) (r : Pset (α × α)) : Pset (α × α) :=
  let oneStep (r : Pset (α × α)) : Pset (α × α) :=
    fold (fun (x, y) xs =>
      fold (fun (y', z) xs =>
        match cmp (y, y) (y', y') with
        | .EQ => add cmp (x, z) xs
        | _ => xs) r xs) r Empty
  let n := cardinal r
  lfpGo cmp oneStep ((2 * n) * (2 * n) + 1) r

/-- pset.ml:360 `set_case` (a singleton is exactly the shape
    `Node (Empty, v, Empty, _)`) -/
def setCase (s : Pset α) (cEmp : β) (cSing : α → β) (cElse : β) : β :=
  match s with
  | Empty => cEmp
  | Node Empty v Empty _ => cSing v
  | _ => cElse

/-- pset.ml:524 `choose_and_split` — the ROOT and its subtrees -/
def chooseAndSplit (s : Pset α) : Option (Pset α × α × Pset α) :=
  match s with
  | Empty => none
  | Node l v r _ => some (l, v, r)

end Pset

/- ---- the lem `set` API (library/set.lem, set_extra.lem, set_helpers.lem
        Lean target reps) over `Pset` ---- -/

def setEmpty : Pset α := .Empty
@[inline] def setIsEmpty (s : Pset α) : Bool := Pset.isEmpty s
def setSingleton (x : α) : Pset α := Pset.singleton x
def setMemberBy (cmp : α → α → LemOrdering) (x : α) (s : Pset α) : Bool := Pset.mem cmp x s
def setAddBy (cmp : α → α → LemOrdering) (x : α) (s : Pset α) : Pset α := Pset.add cmp x s
def setRemoveBy (cmp : α → α → LemOrdering) (x : α) (s : Pset α) : Pset α := Pset.remove cmp x s
@[inline] def setCardinal (s : Pset α) : Nat := Pset.cardinal s
def setFromListBy (cmp : α → α → LemOrdering) (l : List α) : Pset α := Pset.fromList cmp l
def setToList (s : Pset α) : List α := Pset.elements s
def setEqualBy (cmp : α → α → LemOrdering) (s1 s2 : Pset α) : Bool := Pset.equal cmp s1 s2
def setCompareBy (cmp : α → α → LemOrdering) (s1 s2 : Pset α) : LemOrdering := Pset.compare cmp s1 s2
def setUnionBy (cmp : α → α → LemOrdering) (s1 s2 : Pset α) : Pset α := Pset.union cmp s1 s2
def setInterBy (cmp : α → α → LemOrdering) (s1 s2 : Pset α) : Pset α := Pset.inter cmp s1 s2
def setDiffBy (cmp : α → α → LemOrdering) (s1 s2 : Pset α) : Pset α := Pset.diff cmp s1 s2
def setSubsetBy (cmp : α → α → LemOrdering) (s1 s2 : Pset α) : Bool := Pset.subset cmp s1 s2
/-- pset.ml:328 `subset_proper s1 s2 = subset s1 s2 && not (equal s1 s2)` -/
def setProperSubsetBy (cmp : α → α → LemOrdering) (s1 s2 : Pset α) : Bool :=
  Pset.subset cmp s1 s2 && !(Pset.equal cmp s1 s2)
def setFilterBy (cmp : α → α → LemOrdering) (p : α → Bool) (s : Pset α) : Pset α := Pset.filter cmp p s
def setMapBy (cmp : β → β → LemOrdering) (f : α → β) (s : Pset α) : Pset β := Pset.map cmp f s
def setBigunionBy (cmp : α → α → LemOrdering) (xss : Pset (Pset α)) : Pset α := Pset.bigunion cmp xss
def setBigunionMapBy (cmp : β → β → LemOrdering) (f : α → Pset β) (s : Pset α) : Pset β := Pset.mapUnion cmp f s
def setSigmaBy (cmp : (α × β) → (α × β) → LemOrdering) (s : Pset α) (f : α → Pset β) : Pset (α × β) := Pset.sigma cmp s f
def setCrossBy (cmp : (α × β) → (α × β) → LemOrdering) (s1 : Pset α) (s2 : Pset β) : Pset (α × β) := Pset.cross cmp s1 s2
@[inline] def setAny (f : α → Bool) (s : Pset α) : Bool := Pset.exists_ f s
@[inline] def setForAll (f : α → Bool) (s : Pset α) : Bool := Pset.forAll f s
def setFold (f : α → β → β) (s : Pset α) (init : β) : β := Pset.fold f s init
def setCase (s : Pset α) (empty : β) (single : α → β) (otherwise : β) : β := Pset.setCase s empty single otherwise
def setChoose [Inhabited α] (_cmp : α → α → LemOrdering) (s : Pset α) : α := Pset.choose s
def chooseAndSplit (s : Pset α) : Option (Pset α × α × Pset α) := Pset.chooseAndSplit s
/-- pset.ml:350/354 `min_elt_opt` / `max_elt_opt` (lem Set.findMin / findMax) -/
def setFindMin (s : Pset α) : Option α := Pset.minElt? s
def setFindMax (s : Pset α) : Option α := Pset.maxElt? s
def set_tcByCmp (cmp : (α × α) → (α × α) → LemOrdering) (r : Pset (α × α)) : Pset (α × α) := Pset.tc cmp r
/-- lem `Set.leastFixedPoint bound f x` (set.lem; the OCaml is the lem
    definition itself: `if bound = 0 then x else let fx = f x in if fx subset x
    then x else leastFixedPoint (bound-1) f (fx union x)`) -/
def lemLeastFixedPoint (cmp : α → α → LemOrdering) (bound : Nat)
    (f : Pset α → Pset α) (x : Pset α) : Pset α :=
  match bound with
  | 0 => x
  | bound + 1 =>
    let fx := f x
    if Pset.subset cmp fx x then x
    else lemLeastFixedPoint cmp bound f (Pset.union cmp fx x)

/-- Structural instances for `deriving BEq, Ord` on generated types that
    carry a set field: the ascending element spines. NOTE (a ruled
    OCaml-target deviation, DESIGN's deviation list): OCaml's polymorphic compare
    RAISES `Invalid_argument "compare: functional value"` on a Pset
    record (it carries its comparator closure) unless the closures are
    physically identical; lem's own set equality (`setEqualBy`) is the
    comparator-keyed `Pset.equal` above. -/
instance [BEq α] : BEq (Pset α) where
  beq s1 s2 := Pset.elements s1 == Pset.elements s2
instance [Ord α] : Ord (Pset α) where
  compare s1 s2 := compare (Pset.elements s1) (Pset.elements s2)

/- ============================================================================
   Finite maps: Lean translation of ocaml-lib/pmap.ml
   ============================================================================ -/

/-- pmap.ml:16 `type ('key,'a) rep = Empty | Node of rep * 'key * 'a * rep * int` -/
inductive Pmap (α β : Type) : Type where
  | Empty : Pmap α β
  | Node : Pmap α β → α → β → Pmap α β → Nat → Pmap α β

instance : Inhabited (Pmap α β) := ⟨.Empty⟩

namespace Pmap
variable {α β γ : Type}

/-- pmap.ml:20 -/
def height : Pmap α β → Nat
  | Empty => 0
  | Node _ _ _ _ h => h

/-- pmap.ml:24 -/
def create (l : Pmap α β) (x : α) (d : β) (r : Pmap α β) : Pmap α β :=
  let hl := height l
  let hr := height r
  Node l x d r (if hl >= hr then hl + 1 else hr + 1)

/-- pmap.ml:28 -/
def singleton (x : α) (d : β) : Pmap α β := Node Empty x d Empty 1

/-- pmap.ml:30 `bal` -/
def bal (l : Pmap α β) (x : α) (d : β) (r : Pmap α β) : Pmap α β :=
  let hl := height l
  let hr := height r
  if hl > hr + 2 then
    match l with
    | Empty => failwithI "Map.bal"
    | Node ll lv ld lr _ =>
      if height ll >= height lr then create ll lv ld (create lr x d r)
      else match lr with
        | Empty => failwithI "Map.bal"
        | Node lrl lrv lrd lrr _ => create (create ll lv ld lrl) lrv lrd (create lrr x d r)
  else if hr > hl + 2 then
    match r with
    | Empty => failwithI "Map.bal"
    | Node rl rv rd rr _ =>
      if height rr >= height rl then create (create l x d rl) rv rd rr
      else match rl with
        | Empty => failwithI "Map.bal"
        | Node rll rlv rld rlr _ => create (create l x d rll) rlv rld (create rlr rv rd rr)
  else Node l x d r (if hl >= hr then hl + 1 else hr + 1)

/-- pmap.ml:67 `add` — a comparator-EQ binding is REPLACED: the NEW key
    `x` and the new datum are stored (`Node(l, x, data, r, h)`). -/
def add (cmp : α → α → LemOrdering) (x : α) (data : β) : Pmap α β → Pmap α β
  | Empty => Node Empty x data Empty 1
  | Node l v d r h =>
    match cmp x v with
    | .EQ => Node l x data r h
    | .LT => bal (add cmp x data l) v d r
    | .GT => bal l v d (add cmp x data r)

/-- pmap.ml:79 `find` (Not_found → none; pmap.ml:315 `lookup`) -/
def find? (cmp : α → α → LemOrdering) (x : α) : Pmap α β → Option β
  | Empty => none
  | Node l v d r _ =>
    match cmp x v with
    | .EQ => some d
    | .LT => find? cmp x l
    | .GT => find? cmp x r

/-- pmap.ml:94 `min_binding` -/
def minBinding? : Pmap α β → Option (α × β)
  | Empty => none
  | Node Empty x d _ _ => some (x, d)
  | Node l _ _ _ _ => minBinding? l

/-- pmap.ml:104 `remove_min_binding` -/
def removeMinBinding : Pmap α β → Pmap α β
  | Empty => failwithI "Map.remove_min_elt"
  | Node Empty _ _ r _ => r
  | Node l x d r _ => bal (removeMinBinding l) x d r

/-- pmap.ml:109 `merge` (two trees, all keys of t1 below those of t2) -/
def merge2 (t1 t2 : Pmap α β) : Pmap α β :=
  match t1, t2 with
  | Empty, t => t
  | t, Empty => t
  | _, _ =>
    match minBinding? t2 with
    | some (x, d) => bal t1 x d (removeMinBinding t2)
    | none => failwithI "Map.merge: unreachable (non-empty tree without a minimum)"

/-- pmap.ml:117 `remove` -/
def remove (cmp : α → α → LemOrdering) (x : α) : Pmap α β → Pmap α β
  | Empty => Empty
  | Node l v d r _ =>
    match cmp x v with
    | .EQ => merge2 l r
    | .LT => bal (remove cmp x l) v d r
    | .GT => bal l v d (remove cmp x r)

/-- pmap.ml:134 `map` (left, datum, right — the OCaml's let-sequence) -/
def map (f : β → γ) : Pmap α β → Pmap α γ
  | Empty => Empty
  | Node l v d r h =>
    let l' := map f l
    let d' := f d
    let r' := map f r
    Node l' v d' r' h

/-- pmap.ml:143 `mapi` -/
def mapi (f : α → β → γ) : Pmap α β → Pmap α γ
  | Empty => Empty
  | Node l v d r h =>
    let l' := mapi f l
    let d' := f v d
    let r' := mapi f r
    Node l' v d' r' h

/-- pmap.ml:152 `fold` — ascending -/
def fold (f : α → β → γ → γ) : Pmap α β → γ → γ
  | Empty, accu => accu
  | Node l v d r _, accu => fold f r (f v d (fold f l accu))

/-- pmap.ml:158 `for_all` -/
def forAll (p : α → β → Bool) : Pmap α β → Bool
  | Empty => true
  | Node l v d r _ => p v d && forAll p l && forAll p r

/-- Heights consistent with the shape (see `Pset.heightsOk`). -/
def heightsOk : Pmap α β → Bool
  | Empty => true
  | Node l _ _ r h =>
    let hl := height l
    let hr := height r
    h == (if hl >= hr then hl + 1 else hr + 1) && heightsOk l && heightsOk r

/-- pmap.ml:185 `join` — height-indexed structural recursion (see
    `Pset.joinGo` for the rationale; `LemLibTheorems.PmapJoin.join_eq` is the
    equality to the former well-founded definition under `heightsOk`). -/
def joinGo (cmp : α → α → LemOrdering) : Nat → Pmap α β → α → β → Pmap α β → Pmap α β
  | 0, l, _, _, _ => fuelExhaustedWith "Pmap.join: height index exhausted (unreachable: AVL heights bound the recursion)" l
  | h + 1, l, v, d, r =>
    match l, r with
    | Empty, _ => add cmp v d r
    | _, Empty => add cmp v d l
    | Node ll lv ld lr lh, Node rl rv rd rr rh =>
      if lh > rh + 2 then bal ll lv ld (joinGo cmp h lr v d (Node rl rv rd rr rh))
      else if rh > lh + 2 then bal (joinGo cmp h (Node ll lv ld lr lh) v d rl) rv rd rr
      else create l v d r

def join (cmp : α → α → LemOrdering) (l : Pmap α β) (v : α) (d : β) (r : Pmap α β) : Pmap α β :=
  joinGo cmp (height l + height r + 1) l v d r

/-- pmap.ml:196 `concat` -/
def concat (cmp : α → α → LemOrdering) (t1 t2 : Pmap α β) : Pmap α β :=
  match t1, t2 with
  | Empty, t => t
  | t, Empty => t
  | _, _ =>
    match minBinding? t2 with
    | some (x, d) => join cmp t1 x d (removeMinBinding t2)
    | none => failwithI "Map.concat: unreachable (non-empty tree without a minimum)"

/-- pmap.ml:204 `concat_or_join` -/
def concatOrJoin (cmp : α → α → LemOrdering) (t1 : Pmap α β) (v : α) (d : Option β) (t2 : Pmap α β) : Pmap α β :=
  match d with
  | some d => join cmp t1 v d t2
  | none => concat cmp t1 t2

/-- pmap.ml:209 `split` -/
def split (cmp : α → α → LemOrdering) (x : α) : Pmap α β → Pmap α β × Option β × Pmap α β
  | Empty => (Empty, none, Empty)
  | Node l v d r _ =>
    match cmp x v with
    | .EQ => (l, some d, r)
    | .LT => let (ll, pres, rl) := split cmp x l; (ll, pres, join cmp rl v d r)
    | .GT => let (lr, pres, rr) := split cmp x r; (join cmp l v d lr, pres, rr)

/-- pmap.ml:220 `merge cmp f s1 s2` — the general merge (Pmap.union is
    `merge (fun _ o1 o2 -> match o1, o2 with (_, Some v) -> Some v | (Some v, _) -> Some v | _ -> None)`,
    pmap.ml:290); height-fuelled. -/
def mergeGo (cmp : α → α → LemOrdering) (f : α → Option β → Option β → Option β) :
    Nat → Pmap α β → Pmap α β → Pmap α β
  | 0, s1, _ => fuelExhaustedWith "Pmap.merge: height fuel exhausted (unreachable)" s1
  | fuel + 1, s1, s2 =>
    match s1, s2 with
    | Empty, Empty => Empty
    | Node l1 v1 d1 r1 h1, _ =>
      if h1 >= height s2 then
        let (l2, d2, r2) := split cmp v1 s2
        concatOrJoin cmp (mergeGo cmp f fuel l1 l2) v1 (f v1 (some d1) d2) (mergeGo cmp f fuel r1 r2)
      else
        match s2 with
        | Node l2 v2 d2 r2 _ =>
          let (l1, d1, r1) := split cmp v2 s1
          concatOrJoin cmp (mergeGo cmp f fuel l1 l2) v2 (f v2 d1 (some d2)) (mergeGo cmp f fuel r1 r2)
        | Empty => failwithI "Map.merge: unreachable (h1 < height Empty)"
    | Empty, Node l2 v2 d2 r2 _ =>
      let (l1, d1, r1) := split cmp v2 s1
      concatOrJoin cmp (mergeGo cmp f fuel l1 l2) v2 (f v2 d1 (some d2)) (mergeGo cmp f fuel r1 r2)

def merge (cmp : α → α → LemOrdering) (f : α → Option β → Option β → Option β) (s1 s2 : Pmap α β) : Pmap α β :=
  mergeGo cmp f (height s1 + height s2 + 1) s1 s2

/-- pmap.ml:290 `union a b` — b's datum wins on a common key; WHICH key
    survives follows the merge traversal (a's when a's node is visited
    first). -/
def union (cmp : α → α → LemOrdering) (a b : Pmap α β) : Pmap α β :=
  merge cmp (fun _ o1 o2 =>
    match o1, o2 with
    | _, some v => some v
    | some v, _ => some v
    | _, _ => none) a b

/-- pmap.ml:232 enumeration / `cons_enum` -/
inductive Enum (α β : Type) : Type where
  | End : Enum α β
  | More : α → β → Pmap α β → Enum α β → Enum α β

def consEnum : Pmap α β → Enum α β → Enum α β
  | Empty, e => e
  | Node l v d r _, e => consEnum l (.More v d r e)

/-- pmap.ml:265 `cardinal` -/
def cardinal : Pmap α β → Nat
  | Empty => 0
  | Node l _ _ r _ => cardinal l + 1 + cardinal r

/-- pmap.ml:253 `equal cmp_key cmp_a m1 m2` — keys by the map's comparator -/
def equalAux (cmp : α → α → LemOrdering) (eqV : β → β → Bool) : Nat → Enum α β → Enum α β → Bool
  | 0, _, _ => fuelExhaustedWith "Pmap.equal: fuel exhausted (unreachable: bounded by the binding counts)" false
  | fuel + 1, e1, e2 =>
    match e1, e2 with
    | .End, .End => true
    | .End, _ => false
    | _, .End => false
    | .More v1 d1 r1 e1, .More v2 d2 r2 e2 =>
      (match cmp v1 v2 with | .EQ => true | _ => false) && eqV d1 d2 &&
      equalAux cmp eqV fuel (consEnum r1 e1) (consEnum r2 e2)

def equal (cmp : α → α → LemOrdering) (eqV : β → β → Bool) (m1 m2 : Pmap α β) : Bool :=
  equalAux cmp eqV (cardinal m1 + cardinal m2 + 1) (consEnum m1 .End) (consEnum m2 .End)

/-- pmap.ml:269 `bindings` — ascending -/
def bindingsAux : List (α × β) → Pmap α β → List (α × β)
  | accu, Empty => accu
  | accu, Node l v d r _ => bindingsAux ((v, d) :: bindingsAux accu r) l

def bindings (m : Pmap α β) : List (α × β) := bindingsAux [] m

end Pmap

/-- The lem `map 'k 'v` Lean representation. `empty` is deliberate ABI
    (`lean_box(0)` is a valid empty map for consumer C externs); a
    non-empty map carries the comparator captured at first insert —
    pmap.ml's `{cmp; m}` record — which `fmapEqualBy` needs because
    lem's `mapEqualBy eq_k eq_v` is `Pmap.equal eq_v` on OCaml: keys are
    compared with the MAP's comparator, `eq_k` is ignored
    (library/map.lem:30-32). -/
inductive Fmap (α β : Type) : Type where
  | empty
  | mk (cmp : α → α → LemOrdering) (m : Pmap α β)

instance : Inhabited (Fmap α β) := ⟨.empty⟩

def fmapEmpty : Fmap α β := .empty

def Fmap.rep : Fmap α β → Pmap α β
  | .empty => .Empty
  | .mk _ m => m

/-- pmap.ml:62/284 `is_empty` -/
def fmapIsEmpty (m : Fmap α β) : Bool :=
  match m.rep with
  | .Empty => true
  | _ => false

/-- pmap.ml:285 `add k a m = {m with m = add m.cmp k a m.m}` -/
def fmapAddBy (cmp : α → α → LemOrdering) (k : α) (v : β) : Fmap α β → Fmap α β
  | .empty => .mk cmp (Pmap.add cmp k v .Empty)
  | .mk c m => .mk c (Pmap.add c k v m)

/-- pmap.ml:315 `lookup k m = try Some (find k m) with Not_found -> None` -/
def fmapLookupBy (_cmp : α → α → LemOrdering) (k : α) : Fmap α β → Option β
  | .empty => none
  | .mk c m => Pmap.find? c k m
  -- (the comparator argument is the static instance; the CAPTURED one is
  --  used, as in the OCaml wrapper `find k m = find m.cmp k m.m`)

/-- pmap.ml:287 `remove` -/
def fmapDeleteBy (_cmp : α → α → LemOrdering) (k : α) (m : Fmap α β) : Fmap α β :=
  match m with
  | .empty => .empty
  | .mk c m => .mk c (Pmap.remove c k m)

/-- pmap.ml:308 `bindings_list` / `toSet` — ascending -/
def fmapElements (m : Fmap α β) : List (α × β) := Pmap.bindings m.rep

/-- pmap.ml:316-317 -/
def fmapMap (f : β → γ) : Fmap α β → Fmap α γ
  | .empty => .empty
  | .mk c m => .mk c (Pmap.map f m)
def fmapMapi (f : α → β → γ) : Fmap α β → Fmap α γ
  | .empty => .empty
  | .mk c m => .mk c (Pmap.mapi f m)

/-- Structural instances for `deriving BEq, Ord` on generated types with
    map fields: the ascending binding spines (see the Pset note). -/
instance [BEq α] [BEq β] : BEq (Fmap α β) where
  beq m1 m2 := fmapElements m1 == fmapElements m2
instance [Ord α] [Ord β] : Ord (Fmap α β) where
  compare m1 m2 := compare (fmapElements m1) (fmapElements m2)

/-- pmap.ml:296 `equal f a b = equal a.cmp f a.m b.m`: `eq_k` is IGNORED,
    keys compare with the first map's captured comparator. -/
def fmapEqualBy (_eqK : α → α → Bool) (eqV : β → β → Bool) (m1 m2 : Fmap α β) : Bool :=
  match m1, m2 with
  | .empty, .empty => true
  | .mk c a, b => Pmap.equal c eqV a b.rep
  | .empty, .mk c b => Pmap.equal c eqV .Empty b

/-- pmap.ml:306 `domain m = Pset.from_list m.cmp (List.map fst (bindings m.m))` -/
def fmapDomainBy (cmp : α → α → LemOrdering) (m : Fmap α β) : Pset α :=
  Pset.fromList cmp ((fmapElements m).map Prod.fst)

/-- pmap.ml:307 `range cmp m = Pset.from_list cmp (List.map snd (bindings m.m))` -/
def fmapRangeBy (cmp : β → β → LemOrdering) (m : Fmap α β) : Pset β :=
  Pset.fromList cmp ((fmapElements m).map Prod.snd)

/-- pmap.ml:309 `bindings cmp m = Pset.from_list cmp (bindings m.m)` (lem Map.toSetBy) -/
def fmapToSetBy (cmp : (α × β) → (α × β) → LemOrdering) (m : Fmap α β) : Pset (α × β) :=
  Pset.fromList cmp (fmapElements m)

/-- pmap.ml:299 `for_all` -/
def fmapAll (f : α → β → Bool) (m : Fmap α β) : Bool := Pmap.forAll f m.rep

/-- pmap.ml:289 `union a b = merge ... a b` with a's comparator -/
def fmapUnionBy (_cmp : α → α → LemOrdering) (m1 m2 : Fmap α β) : Fmap α β :=
  match m1, m2 with
  | .empty, .empty => .empty
  | .mk c a, b => .mk c (Pmap.union c a b.rep)
  | .empty, .mk c b => .mk c (Pmap.union c .Empty b)

/- ============================================================================
   Unsupported numeric types
   ============================================================================
   Lem's rational, real, float64, and float32 types have no proper Lean
   implementation. Rather than silently mapping to Int (which produces
   semantically wrong results — e.g., rationalFromFrac 1 3 = 0 via integer
   division), we use distinct opaque types that panic on any operation.

   For proper support: rational needs Mathlib's Rat, real needs Mathlib's Real,
   and float64/float32 need IEEE 754 floats. Coq has similar limitations
   (float64/float32 map to Q, also approximate). -/

structure LemRational where
  private mk :: private val : Unit

structure LemReal where
  private mk :: private val : Unit

structure LemFloat64 where
  private mk :: private val : Unit

structure LemFloat32 where
  private mk :: private val : Unit

instance : Inhabited LemRational := ⟨⟨()⟩⟩
instance : BEq LemRational where beq _ _ := panic! "rational: not supported in Lean backend"
instance : Ord LemRational where compare _ _ := panic! "rational: not supported in Lean backend"
instance : Add LemRational where add _ _ := panic! "rational: not supported in Lean backend"
instance : Sub LemRational where sub _ _ := panic! "rational: not supported in Lean backend"
instance : Mul LemRational where mul _ _ := panic! "rational: not supported in Lean backend"
instance : Div LemRational where div _ _ := panic! "rational: not supported in Lean backend"
instance : Neg LemRational where neg _ := panic! "rational: not supported in Lean backend"
instance : HPow LemRational Int LemRational where hPow _ _ := panic! "rational: not supported in Lean backend"
instance : HPow LemRational Nat LemRational where hPow _ _ := panic! "rational: not supported in Lean backend"
instance : Min LemRational where min _ _ := panic! "rational: not supported in Lean backend"
instance : Max LemRational where max _ _ := panic! "rational: not supported in Lean backend"
instance (n : Nat) : OfNat LemRational n where ofNat := panic! "rational: not supported in Lean backend"

instance : Inhabited LemReal := ⟨⟨()⟩⟩
instance : BEq LemReal where beq _ _ := panic! "real: not supported in Lean backend"
instance : Ord LemReal where compare _ _ := panic! "real: not supported in Lean backend"
instance : Add LemReal where add _ _ := panic! "real: not supported in Lean backend"
instance : Sub LemReal where sub _ _ := panic! "real: not supported in Lean backend"
instance : Mul LemReal where mul _ _ := panic! "real: not supported in Lean backend"
instance : Div LemReal where div _ _ := panic! "real: not supported in Lean backend"
instance : Neg LemReal where neg _ := panic! "real: not supported in Lean backend"
instance : HPow LemReal Int LemReal where hPow _ _ := panic! "real: not supported in Lean backend"
instance : HPow LemReal Nat LemReal where hPow _ _ := panic! "real: not supported in Lean backend"
instance : Min LemReal where min _ _ := panic! "real: not supported in Lean backend"
instance : Max LemReal where max _ _ := panic! "real: not supported in Lean backend"
instance (n : Nat) : OfNat LemReal n where ofNat := panic! "real: not supported in Lean backend"

instance : Inhabited LemFloat64 := ⟨⟨()⟩⟩
instance : BEq LemFloat64 where beq _ _ := panic! "float64: not supported in Lean backend"
instance : Ord LemFloat64 where compare _ _ := panic! "float64: not supported in Lean backend"
instance (n : Nat) : OfNat LemFloat64 n where ofNat := panic! "float64: not supported in Lean backend"

instance : Inhabited LemFloat32 := ⟨⟨()⟩⟩
instance : BEq LemFloat32 where beq _ _ := panic! "float32: not supported in Lean backend"
instance : Ord LemFloat32 where compare _ _ := panic! "float32: not supported in Lean backend"
instance (n : Nat) : OfNat LemFloat32 n where ofNat := panic! "float32: not supported in Lean backend"

/- Target rep wrappers for the rational/real comparison operations (the
   value entry points — numerals, conversions — are the refusal markers in
   the `LemUnsupported` namespace below). `never_extract` on every one of
   them: a generated closed application of such a wrapper (the
   `(0 : rational)` literal inside the generated `NumAbs LemRational`
   instance was one) is otherwise lifted to module initialisation and
   panics at start-up of EVERY binary importing LemLib.Num — silently, and
   fatally under LEAN_ABORT_ON_PANIC=1. -/
@[never_extract] def unsupportedRationalLess (_ _ : LemRational) : Bool :=
  panic! "rational: not supported in Lean backend"
@[never_extract] def unsupportedRationalLessEq (_ _ : LemRational) : Bool :=
  panic! "rational: not supported in Lean backend"
@[never_extract] def unsupportedRationalGreater (_ _ : LemRational) : Bool :=
  panic! "rational: not supported in Lean backend"
@[never_extract] def unsupportedRationalGreaterEq (_ _ : LemRational) : Bool :=
  panic! "rational: not supported in Lean backend"

/- The same for the real operations. -/
@[never_extract] def unsupportedRealLess (_ _ : LemReal) : Bool :=
  panic! "real: not supported in Lean backend"
@[never_extract] def unsupportedRealLessEq (_ _ : LemReal) : Bool :=
  panic! "real: not supported in Lean backend"
@[never_extract] def unsupportedRealGreater (_ _ : LemReal) : Bool :=
  panic! "real: not supported in Lean backend"
@[never_extract] def unsupportedRealGreaterEq (_ _ : LemReal) : Bool :=
  panic! "real: not supported in Lean backend"
@[never_extract] def unsupportedRealAbs (_ : LemReal) : LemReal :=
  panic! "real: not supported in Lean backend"

/- Integer square root (floor of exact sqrt) -/
private partial def natSqrtAux (n guess : Nat) : Nat :=
  let next := (guess + n / guess) / 2
  if next >= guess then guess else natSqrtAux n next

/-- lem integerSqrt = Nat_big_num.sqrt = Z.sqrt: `Invalid_argument "Z.sqrt:
    square root of a negative number"` on a negative argument (an earlier
    Lean rep returned the root of the absolute value; parity probe
    f_sqrt_neg). -/
def integerSqrt (n : Int) : Int :=
  if n < 0 then failwithI "Z.sqrt: square root of a negative number"
  else
    let m := n.natAbs
    if m == 0 then 0 else Int.ofNat (natSqrtAux m m)

/- Target rep wrappers for rational/real decomposition operations -/
@[never_extract] def rationalNumerator (_ : LemRational) : Int :=
  panic! "rational: not supported in Lean backend"
@[never_extract] def rationalDenominator (_ : LemRational) : Int :=
  panic! "rational: not supported in Lean backend"
@[never_extract] def realSqrt (_ : LemReal) : LemReal :=
  panic! "real: not supported in Lean backend"
@[never_extract] def realFloor (_ : LemReal) : Int :=
  panic! "real: not supported in Lean backend"
@[never_extract] def realCeiling (_ : LemReal) : Int :=
  panic! "real: not supported in Lean backend"

/- Integer absolute value returning Int (not Nat) -/
def intAbs (n : Int) : Int := Int.ofNat n.natAbs

/- ============================================================ -/
/- Division and remainder — the OCaml reference semantics          -/
/- ============================================================ -/
/- The OCaml target is the reference semantics of a
   lem program; every lem division/remainder rep below mirrors its OCaml
   rep byte-for-byte, including FAILURE: OCaml raises Division_by_zero
   (native `/`, `mod`, Int32/Int64.div/rem, zarith), so the Lean side
   fails loudly (failwithI — panic, then the Inhabited default; a
   harness under LEAN_ABORT_ON_PANIC=1 fail-stops) instead of the
   silent `x / 0 = 0` totalisation of Lean's core operators.

   * lem `int` (OCaml native int): library/num.lem intDiv/intMod ->
     ocaml-lib/nat_num.ml:12-18
       let int_mod i n = let r = i mod n in if r < 0 then r + n else r
       let int_div i n = let r = i / n in if (i mod n < 0) then r - 1 else r
     over OCaml's truncating `/` and `mod` (Int.tdiv / Int.tmod). This is
     Euclidean for a positive divisor but NOT for a negative one:
     int_div (-7) (-2) = 2, int_mod (-7) (-2) = -3 (2 * -2 + -3 = -7); the
     previous reps (`Int.ediv`/`Int.emod`) gave 4 and 1. Two-target pin:
     tests/comprehensive/parity/probes/p_num_div.lem.
   * lem `int32`/`int64`: nat_num.ml:20-33 — the same shape over
     Int32.div/Int32.rem (truncating, wrapping at min_int / -1), which
     Lean's Int32.div (BitVec.sdiv) / Int32.mod (BitVec.srem) match.
   * lem `nat`/`natural`/`integer`: OCaml `/`,`mod` on non-negative ints
     and zarith's Nat_big_num.div/modulus (Euclidean = Int.ediv/Int.emod)
     — unchanged values, plus the zero guard.
   * integerDiv_t / integerRem_t / integerRem_f (num_extra.lem):
     Z.div / Z.rem / mod_big_int — truncating quotient, dividend-signed
     remainder, non-negative remainder; zero raises. -/

/- `never_extract`: at a concrete type this is a CLOSED term; without the
   attribute the compiler lifted `@lemDivByZero Nat _` to a
   module-initialisation constant — the panic fired (silently: messages
   are off during init) at start-up and every `x / 0` then returned the
   pre-computed default with no failure at the program point. Measured
   in the parity suite (f_div_zero printed "at zero: 0" with no panic). -/
@[never_extract] private def lemDivByZero {α : Type} [Inhabited α] : α :=
  failwithI "Division_by_zero"

def lemIntDiv (i n : Int) : Int :=
  if n == 0 then lemDivByZero
  else let r := Int.tdiv i n; if Int.tmod i n < 0 then r - 1 else r
def lemIntMod (i n : Int) : Int :=
  if n == 0 then lemDivByZero
  else let r := Int.tmod i n; if r < 0 then r + n else r

def lemNatDiv (a b : Nat) : Nat := if b == 0 then lemDivByZero else a / b
def lemNatMod (a b : Nat) : Nat := if b == 0 then lemDivByZero else a % b

def lemIntegerDiv (a b : Int) : Int := if b == 0 then lemDivByZero else a / b
def lemIntegerMod (a b : Int) : Int := if b == 0 then lemDivByZero else a % b

def lemInt32Div (i n : Int32) : Int32 :=
  if n == 0 then lemDivByZero
  else let r := i / n; if i % n < 0 then r - 1 else r
def lemInt32Mod (i n : Int32) : Int32 :=
  if n == 0 then lemDivByZero
  else let r := i % n; if r < 0 then r + n else r
def lemInt64Div (i n : Int64) : Int64 :=
  if n == 0 then lemDivByZero
  else let r := i / n; if i % n < 0 then r - 1 else r
def lemInt64Mod (i n : Int64) : Int64 :=
  if n == 0 then lemDivByZero
  else let r := i % n; if r < 0 then r + n else r

/- ============================================================ -/
/- Fixed-width integer types                                   -/
/- ============================================================ -/
/- lem `int32`/`int64` are Lean's `Int32`/`Int64` — two's-complement
   machine integers whose arithmetic WRAPS exactly like OCaml's
   Int32/Int64. Conversions mirror the OCaml reps of
   library/num.lem one by one:
   * Int32.of_int / Int64.of_int (int32FromInt, int32FromNat, ...): the
     argument is taken modulo 2^32 / 2^64 — Int32.ofInt / Int64.ofInt;
   * Nat_big_num.to_int32 / to_int64 (…FromInteger, …FromNatural,
     …FromNumeral): on the OCaml target zarith raises Overflow outside
     the range; lem's OWN semantics of these conversions is MODULAR —
     the prover-side reps are `word_of_int` (Isabelle) / `n2w` (HOL),
     library/num.lem:831-832, :1040-1041, :2378-2470 — so the Lean side
     wraps (Int32.ofInt / Int32.ofNat, Int64 likewise). The raise is an
     OCaml-execution artifact, not mirrored ([USER 2026-09-04];
     doc/lean-backend/2026-09-03_exception-case-rulings.md, D4 addendum;
     parity row f_int32_overflow is a registered OCaml-target deviation);
   * Int64.to_int32 (int32FromInt64): the low 32 bits — Int64.toInt32
     (signExtend to the smaller width truncates); Int64.of_int32
     (int64FromInt32): sign extension — Int32.toInt64;
   * Nat_big_num.of_int32/of_int64 (integerFromInt32/64): exact — .toInt.
   Int32.abs / Int32.neg wrap at min_int on both targets (BitVec.abs /
   two's-complement negation). Comparisons are signed on both.
   Bitwise: Int32.logand/logor/logxor/lognot and the three shifts
   (shift_left, shift_right = arithmetic, shift_right_logical) map onto
   Lean's &&& ||| ^^^ ~~~ and <<< / >>> (arithmetic) / the UInt32
   logical shift; shift amounts are reduced modulo the width on both
   targets on x86-64 (OCaml leaves amounts >= width unspecified). -/

def lemInt32Ltb (a b : Int32) : Bool := decide (a < b)
def lemInt32Lteb (a b : Int32) : Bool := decide (a <= b)
def lemInt32Gtb (a b : Int32) : Bool := decide (b < a)
def lemInt32Gteb (a b : Int32) : Bool := decide (b <= a)
def lemInt32OfNat (n : Nat) : Int32 := Int32.ofNat n
def lemInt32OfInt (i : Int) : Int32 := Int32.ofInt i
/- int32FromNumeral: lem's `n2w`/`word_of_int` — modular (see above). -/
def lemInt32FromNumeral (n : Nat) : Int32 := Int32.ofNat n
def lemInt32ToInt (n : Int32) : Int := n.toInt
def lemInt32FromInt64 (n : Int64) : Int32 := n.toInt32

def lemInt64Ltb (a b : Int64) : Bool := decide (a < b)
def lemInt64Lteb (a b : Int64) : Bool := decide (a <= b)
def lemInt64Gtb (a b : Int64) : Bool := decide (b < a)
def lemInt64Gteb (a b : Int64) : Bool := decide (b <= a)
def lemInt64OfNat (n : Nat) : Int64 := Int64.ofNat n
def lemInt64OfInt (i : Int) : Int64 := Int64.ofInt i
/- int64FromNumeral: lem's `n2w`/`word_of_int` — modular (see above). -/
def lemInt64FromNumeral (n : Nat) : Int64 := Int64.ofNat n
def lemInt64ToInt (n : Int64) : Int := n.toInt
def lemInt64FromInt32 (n : Int32) : Int64 := n.toInt64

/- ============================================================ -/
/- Bitwise operations for fixed-width integers                  -/
/- ============================================================ -/
def int32Lnot (x : Int32) : Int32 := ~~~x
def int32Lor (x y : Int32) : Int32 := x ||| y
def int32Lxor (x y : Int32) : Int32 := x ^^^ y
def int32Land (x y : Int32) : Int32 := x &&& y
def int32Lsl (x : Int32) (n : Nat) : Int32 := x <<< Int32.ofNat n
def int32Lsr (x : Int32) (n : Nat) : Int32 := (x.toUInt32 >>> UInt32.ofNat n).toInt32
def int32Asr (x : Int32) (n : Nat) : Int32 := x >>> Int32.ofNat n

def int64Lnot (x : Int64) : Int64 := ~~~x
def int64Lor (x y : Int64) : Int64 := x ||| y
def int64Lxor (x y : Int64) : Int64 := x ^^^ y
def int64Land (x y : Int64) : Int64 := x &&& y
def int64Lsl (x : Int64) (n : Nat) : Int64 := x <<< Int64.ofNat n
def int64Lsr (x : Int64) (n : Nat) : Int64 := (x.toUInt64 >>> UInt64.ofNat n).toInt64
def int64Asr (x : Int64) (n : Nat) : Int64 := x >>> Int64.ofNat n

/- ============================================================ -/
/- Missing library functions -/
/- ============================================================ -/

/-- zarith `Z.of_string` (lem Num_extra.integerOfString = Nat_big_num.of_string),
    grammar as MEASURED against the OCaml reference (parity probe
    p_num_parse): an optional single sign
    (`+`/`-`), an optional base prefix `0x`/`0X` (16), `0o`/`0O` (8),
    `0b`/`0B` (2), then digits of that base in which `_` may appear after
    the first digit ("1_000", "1__0", "1_" accepted; "_1", "0x_1" not);
    the EMPTY digit string reads as 0 ("", "+", "-", "0x", "0b" are 0);
    anything else — whitespace, a second sign, an out-of-base digit,
    "1e3", "1.5" — raises `Invalid_argument "Z.of_substring_base: invalid
    digit"`, which is a loud failure here. -/
def lemIntegerOfString (s : String) : Int :=
  let digitVal (c : Char) : Option Nat :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  let rec go (base acc : Nat) (first : Bool) : List Char → Option Nat
    | [] => some acc
    | '_' :: rest => if first then none else go base acc false rest
    | c :: rest =>
      match digitVal c with
      | some d => if d < base then go base (acc * base + d) false rest else none
      | none => none
  let (neg, cs) := match s.toList with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | cs => (false, cs)
  let (base, cs) := match cs with
    | '0' :: c :: rest =>
      if c == 'x' || c == 'X' then (16, rest)
      else if c == 'o' || c == 'O' then (8, rest)
      else if c == 'b' || c == 'B' then (2, rest)
      else (10, '0' :: c :: rest)
    | cs => (10, cs)
  match go base 0 true cs with
  | some n => if neg then -(Int.ofNat n) else Int.ofNat n
  | none => failwithI "Z.of_substring_base: invalid digit"

/-- lem Num_extra.naturalOfString = Nat_big_num.of_string_nat
    (ocaml-lib/nat_big_num.ml:63-68): `of_string`, then `assert false` if
    the result is negative. -/
def naturalOfString (s : String) : Nat :=
  let i := lemIntegerOfString s
  if i < 0 then failwithI "Assertion failed (Nat_big_num.of_string_nat: negative)"
  else i.toNat

/- ============================================================ -/
/- LemUnsupported — the generation-time refusal markers             -/
/- ============================================================ -/
/- A lem constant or type whose Lean target_rep lives in this namespace
   has NO Lean implementation: the backend REFUSES any reference to it
   from a non-library module at generation time ([USER 2026-09-03]
   exception class (c); `lean_unsupported_check_cref/type` in
   src/lean_backend.ml). The definitions here exist only so the lem
   LIBRARY's own instance code (`instance (Numeral rational) ...`)
   compiles; user code can never call them — a Unit-valued "loud runtime
   refusal" was measured to be DEAD-CODE-ELIMINATED by the compiler
   (`let u = Debug.print_endline "dbg" in ...` printed nothing and exited
   0 on Lean), which is why the refusal must be at generation time. -/
namespace LemUnsupported
abbrev rational := LemRational
abbrev real := LemReal
abbrev float64 := LemFloat64
abbrev float32 := LemFloat32
@[never_extract] def rationalFromNumeral (_ : Nat) : LemRational := panic! "rational: not supported in Lean backend"
@[never_extract] def rationalFromInt (_ : Int) : LemRational := panic! "rational: not supported in Lean backend"
@[never_extract] def rationalFromFrac (_ _ : Int) : LemRational := panic! "rational: not supported in Lean backend"
@[never_extract] def realFromNumeral (_ : Nat) : LemReal := panic! "real: not supported in Lean backend"
@[never_extract] def realFromInt (_ : Int) : LemReal := panic! "real: not supported in Lean backend"
@[never_extract] def realFromFrac (_ _ : Int) : LemReal := panic! "real: not supported in Lean backend"
/-- lem Debug.print_string / print_endline: the OCaml reference prints to
    stdout; pure Lean code cannot. -/
@[never_extract] def debugPrintString (_s : String) : Unit :=
  panic! "Debug.print_string: unsupported on the Lean target"
@[never_extract] def debugPrintEndline (_s : String) : Unit :=
  panic! "Debug.print_endline: unsupported on the Lean target"
end LemUnsupported

/- lem `natFromNatural` / `intFromInteger`: the IDENTITY on Lean's unbounded
   Nat/Int. lem's semantics for `nat`/`int` is the prover-side, unbounded
   one (library/num.lem:104-111; [USER 2026-09-03] exception-case rulings,
   X3); the OCaml target's `Nat_big_num.to_int` raising `Failure
   "int_of_big_int"` outside [-2^62, 2^62-1] is an OCaml-execution limit,
   not lem's meaning — [USER 2026-09-03]: hardcoded limits that come from
   OCaml-level execution issues are forbidden too; the logical semantics
   is what counts (an earlier rep failed loudly at the
   OCaml bound). The parity runner's `f_int_of_big_num`
   row is a registered OCaml-target deviation (parity/expected_failures.txt).
   natFromNumeral / intFromNumeral keep their literal-passthrough reps. -/
def lemIntFromInteger (i : Int) : Int := i
def lemNatFromNatural (n : Nat) : Nat := n

/- Z.div / Z.rem / mod_big_int (ocaml-lib/nat_big_num.ml integerDiv_t,
   integerRem_t, integerRem_f); zarith raises Division_by_zero on 0. -/
def integerDiv_t (a b : Int) : Int := if b == 0 then lemDivByZero else Int.tdiv a b
def integerRem_t (a b : Int) : Int := if b == 0 then lemDivByZero else Int.tmod a b
def integerRem_f (a b : Int) : Int := if b == 0 then lemDivByZero else Int.emod a b

@[never_extract] def THE (_p : α → Bool) : Option α :=
  panic! "THE: Hilbert choice is not computable"

/- List indexing: the Lean reps of lem `List.index` / `List_extra.nth`
   (`List.get?`/`List.get!` were removed from Lean core). -/
def listGetOpt (l : List α) (n : Nat) : Option α := l[n]?
def listGetBang [Inhabited α] (l : List α) (n : Nat) : α := l[n]!

/- Convert a natural number to a list of bools (binary representation, LSB first) -/
def boolListFromNatural (acc : List Bool) (remainder : Nat) : List Bool :=
  if h : remainder > 0 then
    boolListFromNatural ((remainder % 2 == 1) :: acc) (remainder / 2)
  else
    acc.reverse
termination_by remainder
decreasing_by exact Nat.div_lt_self h (by omega)

/- Bitwise binary operation on two bool lists, extending shorter with sign bit -/
def bitSeqBinopAux (binop : Bool → Bool → Bool) (s1 : Bool) (bl1 : List Bool)
    (s2 : Bool) (bl2 : List Bool) : List Bool :=
  match bl1, bl2 with
  | [], [] => []
  | b1 :: bl1', [] => (binop b1 s2) :: bitSeqBinopAux binop s1 bl1' s2 []
  | [], b2 :: bl2' => (binop s1 b2) :: bitSeqBinopAux binop s1 [] s2 bl2'
  | b1 :: bl1', b2 :: bl2' => (binop b1 b2) :: bitSeqBinopAux binop s1 bl1' s2 bl2'
termination_by bl1.length + bl2.length

/- Nat bitwise operations (the reps of word.lem's nat bitwise functions
   and of transform.lem's). Named lemNat*: as
   `natLand`/`natLor`/`natLxor`/`natLsl`/`natAsr` they
   collided with the generated `Lem_Word.natLand`/... — every direct call
   of Word's nat bitwise functions from a lem program was an "Ambiguous
   term" Lean build error. Regression: parity probe p_lib_word_int_nat. -/
def lemNatLand (a b : Nat) : Nat := a &&& b
def lemNatLor (a b : Nat) : Nat := a ||| b
def lemNatLxor (a b : Nat) : Nat := a ^^^ b
@[never_extract] def lemNatLnot (_a : Nat) : Nat := panic! "lemNatLnot: bitwise NOT is not defined for Nat"
def lemNatLsl (a b : Nat) : Nat := a <<< b
def lemNatLsr (a b : Nat) : Nat := a >>> b
def lemNatAsr (a b : Nat) : Nat := a >>> b  -- same as lsr for Nat (unsigned)

/- Int bitwise operations: UNBOUNDED two's complement, the Lean reps of
   word.lem's intLand/intLor/intLxor/intLsl/intAsr (a ruled OCaml-target
   deviation: [USER 2026-09-30] agreed items 1-3; probe
   p_word_bitwise_wide, class ruled). The OCaml
   reference is native 63-bit `land`/`lor`/`lxor`/`lsl`/`asr`; these agree
   with it on its whole domain and DIFFER where OCaml wraps (the accepted
   deviation). Lem's
   own definitions go through a 31-bit bitSequence and disagreed from 2^30
   on. `Int.negSucc n` is `-(n+1)`, i.e. the complement `~~~n` of `n`, so
   each case is a Nat identity: `a &&& ~~~b = a ^^^ (a &&& b)`,
   `~~~a &&& ~~~b = ~~~(a ||| b)`, `~~~a ^^^ b = ~~~(a ^^^ b)`, ... -/
def lemIntLand : Int → Int → Int
  | .ofNat a,   .ofNat b   => .ofNat (a &&& b)
  | .ofNat a,   .negSucc b => .ofNat (a ^^^ (a &&& b))
  | .negSucc a, .ofNat b   => .ofNat (b ^^^ (b &&& a))
  | .negSucc a, .negSucc b => .negSucc (a ||| b)
def lemIntLor : Int → Int → Int
  | .ofNat a,   .ofNat b   => .ofNat (a ||| b)
  | .ofNat a,   .negSucc b => .negSucc (b ^^^ (b &&& a))
  | .negSucc a, .ofNat b   => .negSucc (a ^^^ (a &&& b))
  | .negSucc a, .negSucc b => .negSucc (a &&& b)
def lemIntLxor : Int → Int → Int
  | .ofNat a,   .ofNat b   => .ofNat (a ^^^ b)
  | .ofNat a,   .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .ofNat b   => .negSucc (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)
def lemIntLsl (a : Int) (n : Nat) : Int := a <<< n
def lemIntAsr (a : Int) (n : Nat) : Int := a >>> n  -- Int.shiftRight: floor division by 2^n

/- ============================================================ -/
/- Deep lists: explicitly tail-recursive library functions       -/
/- ============================================================ -/
/- [USER 2026-09-03] exception class (b): Lean must not fail where the
   OCaml reference succeeds. The compiled Lean binary
   has a fixed native stack; OCaml 5 grows its stack. A 300 000-element
   sweep over the library (tests/comprehensive/parity/probes/p_list_deep.lem,
   record) aborted with "Stack overflow detected" on: core `List.zip`
   and `List.unzip` as called from generated code, the generated
   `Lem_String.concat`, `Lem_Show.stringFromListAux`, `Lem_List.deleteFirst`,
   `update`, `catMaybes`, `mapiAux`, `Lem_List_extra.init`,
   `zipSameLength`, `unfoldr`, `Lem_Sorting.insertBy`, and `List.foldr`
   as called from `Lem_List_extra.foldr1`. The core `@[csimp]`
   tail-recursive replacements were measured NOT to apply reliably at
   these call sites (the same `List.foldr` call worked or overflowed
   depending on the enclosing definition), so nothing below relies on
   csimp: every function is an explicit accumulator loop (self tail
   call → compiled as a loop) or an `Array` fold, and the lem library
   reps point here. Each has a kernel-checked equality theorem against
   the definition it replaces in lean-lib/LemLibTheorems.lean (built
   with the library; `unfoldr` is `partial` on both sides and admits no
   theorem — recorded there). -/

/-- `List.zip` (lem List.zip): accumulator loop, then reverse. -/
def lemListZipAux : List α → List β → List (α × β) → List (α × β)
  | x :: xs, y :: ys, acc => lemListZipAux xs ys ((x, y) :: acc)
  | _, _, acc => acc.reverse
def lemListZip (l1 : List α) (l2 : List β) : List (α × β) := lemListZipAux l1 l2 []

/-- `List.unzip` (lem List.unzip) -/
def lemListUnzipAux : List (α × β) → List α → List β → List α × List β
  | [], as, bs => (as.reverse, bs.reverse)
  | (a, b) :: l, as, bs => lemListUnzipAux l (a :: as) (b :: bs)
def lemListUnzip (l : List (α × β)) : List α × List β := lemListUnzipAux l [] []

/-- `List.foldr` (lem List.foldr): an Array fold — a loop over indices. -/
def lemListFoldr (f : α → β → β) (init : β) (l : List α) : β := l.toArray.foldr f init

/-- lem List.deleteFirst: `match l with [] -> Nothing | x::xs -> if P x then Just xs
    else Maybe.map (fun xs' -> x::xs') (deleteFirst P xs)` -/
def lemListDeleteFirstAux (P : α → Bool) : List α → List α → Option (List α)
  | [], _ => none
  | x :: xs, acc => if P x then some (acc.reverseAux xs) else lemListDeleteFirstAux P xs (x :: acc)
def lemListDeleteFirst (P : α → Bool) (l : List α) : Option (List α) := lemListDeleteFirstAux P l []

/-- lem List.update: `[] -> [] | x::xs -> if n = 0 then e::xs else x :: update xs (n-1) e` -/
def lemListUpdateAux (e : α) : List α → Nat → List α → List α
  | [], _, acc => acc.reverse
  | x :: xs, n, acc => if n == 0 then acc.reverseAux (e :: xs) else lemListUpdateAux e xs (n - 1) (x :: acc)
def lemListUpdate (l : List α) (n : Nat) (e : α) : List α := lemListUpdateAux e l n []

/-- lem List.catMaybes -/
def lemListCatMaybesAux : List (Option α) → List α → List α
  | [], acc => acc.reverse
  | none :: xs, acc => lemListCatMaybesAux xs acc
  | some x :: xs, acc => lemListCatMaybesAux xs (x :: acc)
def lemListCatMaybes (xs : List (Option α)) : List α := lemListCatMaybesAux xs []

/-- lem List.mapiAux / mapi -/
def lemListMapiAuxAcc (f : Nat → α → β) : Nat → List α → List β → List β
  | _, [], acc => acc.reverse
  | n, x :: xs, acc => lemListMapiAuxAcc f (n + 1) xs (f n x :: acc)
def lemListMapi (f : Nat → α → β) (l : List α) : List β := lemListMapiAuxAcc f 0 l []

/-- lem List_extra.init: all but the last element; `[]` fails loudly on
    both targets (the OCaml lem definition is `failwith`). -/
def lemListInitAux : List α → List α → List α
  | [_], acc => acc.reverse
  | x1 :: x2 :: xs, acc => lemListInitAux (x2 :: xs) (x1 :: acc)
  | [], acc => acc.reverse  -- unreachable from lemListInit (the [] case is handled there)
def lemListInit (l : List α) : List α :=
  match l with
  | [] => failwithI "List_extra.init of empty list"
  | _ => lemListInitAux l []

/-- lem List_extra.zipSameLength (OCaml `List.combine`: Invalid_argument on
    unequal lengths). -/
def lemListZipSameLengthAux : List α → List β → List (α × β) → List (α × β)
  | x :: xs, y :: ys, acc => lemListZipSameLengthAux xs ys ((x, y) :: acc)
  | [], [], acc => acc.reverse
  | _, _, _ => failwithI "List_extra.zipSameLength of different length lists"
def lemListZipSameLength (l1 : List α) (l2 : List β) : List (α × β) := lemListZipSameLengthAux l1 l2 []

/-- lem List_extra.unfoldr (partial on both targets: the OCaml lem
    definition loops as long as `f` yields `Just`). -/
partial def lemListUnfoldrAux (f : α → Option (β × α)) (x : α) (acc : List β) : List β :=
  match f x with
  | some (y, x') => lemListUnfoldrAux f x' (y :: acc)
  | none => acc.reverse
partial def lemListUnfoldr (f : α → Option (β × α)) (x : α) : List β := lemListUnfoldrAux f x []

/-- lem Sorting.insertBy: `[] -> [e] | x::xs -> if cmp x e then x :: insertBy cmp e xs else e::x::xs` -/
def lemInsertByAux (cmp : α → α → Bool) (e : α) : List α → List α → List α
  | [], acc => acc.reverseAux [e]
  | x :: xs, acc => if cmp x e then lemInsertByAux cmp e xs (x :: acc) else acc.reverseAux (e :: x :: xs)
def lemInsertBy (cmp : α → α → Bool) (e : α) (l : List α) : List α := lemInsertByAux cmp e l []

/-- lem String.concat / Show.stringFromListAux: `sep`-separated join —
    `[] -> "" | [s] -> s | s::ss -> s ^ sep ^ concat sep ss`. -/
def lemStringJoinAux (sep : String) : List String → String → String
  | [], acc => acc
  | s :: ss, acc => lemStringJoinAux sep ss (acc ++ sep ++ s)
def lemStringJoin (sep : String) : List String → String
  | [] => ""
  | s :: ss => lemStringJoinAux sep ss s
def lemStringConcat (sep : String) (ss : List String) : String := lemStringJoin sep ss
def lemShowListAux (showX : α → String) (xs : List α) : String := lemStringJoin "; " (xs.map showX)

/- ============================================================ -/
/- Total implementations for generated library functions         -/
/- ============================================================ -/

/- Total stringFromNatHelper: converts nat to digit chars via n/10 recursion -/
def lemStringFromNatHelper (n : Nat) (acc : List Char) : List Char :=
  if h : n = 0 then acc
  else lemStringFromNatHelper (n / 10) (Char.ofNat ((n % 10) + 48) :: acc)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/- String_extra.chr: a lem `char` is a byte (OCaml `char`; HOL CHR and Isabelle
   char_of are 8-bit). The OCaml reference `Char.chr` raises
   `Invalid_argument "Char.chr"` outside 0..255; the previous rep
   `Char.ofNat` returned the Unicode scalar (chr 256 = 'Ā', ord of it 256)
   and succeeded where the reference fails. Fail loudly instead.
   (0..255 → Char.ofNat as before; bytes 128..255 as Unicode scalars are
   the strings-as-bytes design, TODO item 31, not this fix.) Regression: failure probe
   f_lib_chr_range. -/
def lemChr (n : Nat) : Char :=
  if n < 256 then Char.ofNat n else failwithI "Invalid_argument(\"Char.chr\")"

/- Total stringFromNaturalHelper: identical logic (natural = nat in Lean) -/
def lemStringFromNaturalHelper (n : Nat) (acc : List Char) : List Char :=
  if h : n = 0 then acc
  else lemStringFromNaturalHelper (n / 10) (Char.ofNat ((n % 10) + 48) :: acc)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/- ========================================================================
   Machine word (mword / BitVec) operations
   ======================================================================== -/

/- Conversion operations -/
def mwordFromInteger {n : Nat} (i : Int) : BitVec n := BitVec.ofInt n i
def mwordFromNatural {n : Nat} (i : Nat) : BitVec n := BitVec.ofNat n i
def mwordSignedToInteger {n : Nat} (w : BitVec n) : Int := w.toInt
def mwordUnsignedToInteger {n : Nat} (w : BitVec n) : Int := Int.ofNat w.toNat
def mwordNaturalFromWord {n : Nat} (w : BitVec n) : Nat := w.toNat

/- Bitwise operations -/
def mwordLAnd {n : Nat} (a b : BitVec n) : BitVec n := a &&& b
def mwordLOr {n : Nat} (a b : BitVec n) : BitVec n := a ||| b
def mwordLXor {n : Nat} (a b : BitVec n) : BitVec n := a ^^^ b
def mwordLNot {n : Nat} (a : BitVec n) : BitVec n := ~~~a

/- Shift operations (Lem uses Nat for shift amount) -/
def mwordShiftLeft {n : Nat} (w : BitVec n) (s : Nat) : BitVec n := w <<< s
def mwordShiftRight {n : Nat} (w : BitVec n) (s : Nat) : BitVec n := w >>> s
def mwordArithShiftRight {n : Nat} (w : BitVec n) (s : Nat) : BitVec n := BitVec.sshiftRight w s

/- Rotate operations -/
def mwordRotateLeft {n : Nat} (s : Nat) (w : BitVec n) : BitVec n := BitVec.rotateLeft w s
def mwordRotateRight {n : Nat} (s : Nat) (w : BitVec n) : BitVec n := BitVec.rotateRight w s

/- Bit access -/
def mwordGetBit {n : Nat} (w : BitVec n) (i : Nat) : Bool := w.getLsbD i
def mwordSetBit {n : Nat} (w : BitVec n) (i : Nat) (b : Bool) : BitVec n :=
  if b then w ||| (BitVec.ofNat n (1 <<< i))
  else w &&& ~~~(BitVec.ofNat n (1 <<< i))
def mwordMsb {n : Nat} (w : BitVec n) : Bool := w.msb
def mwordLsb {n : Nat} (w : BitVec n) : Bool := w.getLsbD 0

/- Arithmetic operations -/
def mwordPlus {n : Nat} (a b : BitVec n) : BitVec n := a + b
def mwordMinus {n : Nat} (a b : BitVec n) : BitVec n := a - b
def mwordUminus {n : Nat} (a : BitVec n) : BitVec n := -a
def mwordTimes {n : Nat} (a b : BitVec n) : BitVec n := a * b
/- Division by zero: the OCaml reps (ocaml-lib/lem.ml:240-241 `word_udiv`
   / `word_mod` = Nat_big_num.div / modulus; `signedDivide` is a lem
   definition over them) raise Division_by_zero; BitVec.udiv/umod/sdiv
   totalise to 0 — fail loudly instead. -/
def mwordUnsignedDivide {n : Nat} (a b : BitVec n) : BitVec n :=
  if b == 0 then failwithI "Division_by_zero" else BitVec.udiv a b
def mwordSignedDivide {n : Nat} (a b : BitVec n) : BitVec n :=
  if b == 0 then failwithI "Division_by_zero" else BitVec.sdiv a b
def mwordModulo {n : Nat} (a b : BitVec n) : BitVec n :=
  if b == 0 then failwithI "Division_by_zero" else BitVec.umod a b

/- Comparison operations -/
def mwordEq {n : Nat} (a b : BitVec n) : Bool := a == b
def mwordSignedLess {n : Nat} (a b : BitVec n) : Bool := BitVec.slt a b
def mwordSignedLessEq {n : Nat} (a b : BitVec n) : Bool := BitVec.sle a b
def mwordUnsignedLess {n : Nat} (a b : BitVec n) : Bool := BitVec.ult a b
def mwordUnsignedLessEq {n : Nat} (a b : BitVec n) : Bool := BitVec.ule a b

/- Word concatenation and extraction -/
def mwordConcat {n m result : Nat} (a : BitVec n) (b : BitVec m) : BitVec result :=
  (a ++ b).setWidth result
def mwordExtract {n result : Nat} (lo hi : Nat) (w : BitVec n) : BitVec result :=
  -- Lem passes (lo, hi, word): bits lo..hi, zero-extended/truncated to the
  -- result width. The OCaml reference (lem.ml word_extract: hi-lo+1 bits from
  -- lo) and HOL (words$word_extract hi lo, then w2w) both mask by hi; the
  -- previous rep ignored hi as Isabelle's Word.slice does, and returned
  -- bits beyond hi whenever the result type is wider than hi-lo+1
  -- (word_extract 0 3 (0xAB : mword ty8) : mword ty8 gave 0xAB, not 0xB).
  -- Regression: parity probe p_lib_machine_word.
  (BitVec.extractLsb' lo (hi + 1 - lo) w).setWidth result
def mwordUpdate {n m : Nat} (w : BitVec n) (lo _hi : Nat) (v : BitVec m) : BitVec n :=
  -- Lem passes (word, lo, hi, value); hi is redundant given v's width m.
  let mask := ~~~(BitVec.ofNat n (((1 <<< m) - 1) <<< lo))
  let shifted := BitVec.ofNat n (v.toNat <<< lo)
  (w &&& mask) ||| shifted

/- Width operations -/
def mwordZeroExtend {w v : Nat} (a : BitVec w) : BitVec v := BitVec.zeroExtend v a
def mwordSignExtend {w v : Nat} (a : BitVec w) : BitVec v := BitVec.signExtend v a

/- Word length -/
def mwordLength {n : Nat} (_ : BitVec n) : Nat := n

/- Hex display -/
def mwordToHex {n : Nat} (w : BitVec n) : String := BitVec.toHex w

/- Bitlist conversion -/
/- Bit lists are MOST-significant bit first: lem's own asserts
   (machine_word.lem wordFromBitlist_test / bitlistFromWord_test:
   `wordFromBitlist [false;false;true;false] : mword ty4 = 2`), the OCaml
   reference (lem.ml wordFromBitlist/bitlistFromWord), Isabelle of_bl/to_bl
   and HOL v2w/w2v all read the head as the MSB; these reps read it as the
   LSB. A list longer than the width keeps its low bits (HOL v2w).
   Regression: parity probe p_lib_machine_word. -/
def mwordFromBitlist {n : Nat} (bits : List Bool) : BitVec n :=
  BitVec.ofNat n (bits.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0)

def mwordToBitlist {n : Nat} (w : BitVec n) : List Bool :=
  List.map (fun i => w.getLsbD (n - 1 - i)) (List.range n)


