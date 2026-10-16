/- Arc-8 S2: hand-written signature-shape checks for the [Inhabited]
   threading pass over tests/comprehensive/test_failwith_threading.lem
   (design note doc/notes/2026-08-20_arc8-inhabited-threading-design.md,
   section S2 rules 1-6). Each example uses a def under EXACTLY the
   binders the pass is specified to thread — the binders written here
   are the only Inhabited facts in scope, so success means the def
   demands no more than them; `Empty` instantiations pin that the
   NO-binder defs demand nothing at all. -/
import Test_failwith_threading

/- 1. Bare-tyvar failure site -> [Inhabited a]. -/
example {a : Type} [Inhabited a] (l : List a) : a := first_or_fail l

/- 2. Depth-1 propagation: the caller inherited the binder (and needs
   nothing else). -/
example {a : Type} [Inhabited a] (l : List a) : a := second_or_first l

/- 3. Composite site types -> NO binder: works at an UNINHABITED
   element type, so any spurious [Inhabited] demand would fail here. -/
example (l : List Empty) : List Empty := tail_or_fail l
/- either site: only the LEFT ([Inhabited a]) bound is demanded —
   checked with the right side uninhabited. -/
example {a : Type} [Inhabited a] (l : List (a × Empty)) : Sum a Empty :=
  left_or_fail l

/- 4. L_undefined (incomplete-match arm) at a tyvar type: same
   binder, failwithI body carrying the Incomplete Pattern message
   (audit fix — mirrors OCaml's raise); no sorry, no silent default
   anywhere in its definition. -/
example {a : Type} [Inhabited a] (l : List a) : a := head_undef l

/- 7. Multi-clause emission path: same binder shape. -/
example {a : Type} [Inhabited a] (l : List a) : a := alt_or_fail l

/- Runtime behavior of the panic path is pinned IN THIS SUITE by
   TestFailwithThreadingPanic.lean (Makefile target `lean-panic`:
   abort under LEAN_ABORT_ON_PANIC=1 with the Incomplete Pattern
   message — the harness discipline of cerberus scripts/common.sh),
   and further exercised by the cerberus differential suites
   (byte-identical panic, arc-8 S3 zero-movement bar); the asserts
   in Test_failwith_threading_auxiliary.lean cover the success
   paths. -/
