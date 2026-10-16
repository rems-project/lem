# Lean backend findings from porting linksem (2026-09-28)

Branch `linksem/fixes` (from `mdd/lean-backend` at `c2a68e7`). linksem
(rems-project/linksem: ELF, DWARF and static-linking semantics in Lem,
~34k lines, 96 model modules) was generated with `lem -lean` and compiled
against LemLib as a second large consumer after Cerberus. Every finding
below was hit by real linksem code; each fix carries a regression test in
`tests/comprehensive` (listed per item).

Provenance: [USER 2026-09-28] charter: the main purpose of the exercise is
to see whether it shakes out any bugs in lem-lean; fixes and designs below
are [AGENT] unless marked.

Toolchain: Lean 4.28.0 (the `lean-lib/lean-toolchain` pin). Cerberus builds
on 4.32.2; B9 is toolchain-dependent (see there).

## B1. Constants with symbolic names (fixed)

linksem's `error.lem` defines `let (>>=) x f = bind x f` and uses it infix
throughout. The backend emitted `def >>= ...` (a Lean parse error), and
every infix use `x >>= f` resolved to Lean's own `Bind` operator. Even with
`declare {lean} ascii_rep`, only the definition was renamed: Lem's
`ascii_rep_set` holds the constants a definition *defines* (other targets
accept symbolic names at uses), so uses still printed `>>=`.

Fix: a shown constant whose Lean name is not a Lean identifier is rendered
by its ASCII representation at the definition and at every use (prefix
form, operands parenthesised as arguments). Without an ASCII rep the
definition is refused at generation time, naming the fix. The identifier
test is Lean's grammar (`'` allowed), not Lem's `is_simple_ident_string`.
Tests: `test_symbolic_ops.lem` (infix, prefix, chained, application
operands, partial application), `negative/neg_symbolic_def.lem`.

## B2. No `Ord LemOrdering` (fixed, LemLib)

Sets of comparison results (`Set.member (compare a b) {LT; EQ}`, used in
linksem's orderings) need `SetType ordering`, derived from `Ord`. Added
`instance : Ord LemOrdering` with the OCaml target's order LT < EQ < GT
(`ordering` is `int` there: -1 < 0 < 1). Tests: `LemLibTest.lean` (kernel
`decide` pins on `compare`, `Pset.fromList`, `Pset.mem`).

## B3. If/else-if chains deeper than ~128 (fixed)

Lean 4.28 cannot elaborate an else-if chain nested more than ~128 deep
("maximum recursion depth has been reached"), independent of the branch
contents (measured with synthetic chains of 150 and 600 arms; 100 passes).
linksem's AArch64 relocation dispatch has a 123-arm chain inside a larger
term. A `maxRecDepth` bump is not a fix. Chains of more than 96 arms are
emitted in blocks of 64: each later block is a local continuation
`let _lemIfTailN := fun (_ : Unit) => <block>` (innermost first), and a
block's final `else` calls the next. Pure and order-preserving; `zeta`
unfolds it in proofs. Variables of the chain using the reserved
`_lemIfTail` prefix are refused. Test: `test_long_if_chain.lem` (150 arms;
first, middle, both block boundaries, last and fall-through pinned; the
same shape nested in a `let` inside a `match`).

## B4. Nested inductives through type abbreviations (fixed)

linksem's `dwarf.lem` ties a knot through a parameter:
`type c_type_top 't = ... | CT_array of cupdie * 't * list (array_dimension 't)`
and `type c_type = CT of c_type_top c_type`, where `array_dimension` is an
abbreviation. The kernel rejects the nested occurrence ("arg #1 of
'_nested.List_2.cons' contains a non valid occurrence of the datatypes
being declared") because it does not unfold the emitted `abbrev`; the same
definition with the abbreviation written inline is accepted (6-line
repro). In inductive constructor arguments (and mutual-record fields), an
abbreviation without a Lean target rep whose expansion mentions a type
parameter or a type of the group being defined is printed expanded;
closed abbreviations keep their names. Test: `test_nested_abbrev.lem`.

## B5. Incomplete Lean keyword tables (fixed; checker added)

linksem binds `let matches = List.filter ...`; `matches` is a Lean token,
and the output did not parse. Rather than add one word: the new
`scripts/lean_keyword_probe.sh` derives from the pinned toolchain every
identifier-shaped core-grammar token that fails as a binder (166 on 4.28)
and checks that BOTH avoid lists contain it: `lean_syntax_keywords` in
`src/lean_backend.ml` (local names) and `library/lean_constants`
(top-level names). 86 were missing from the first, 82 from the second
(`matches`, `repeat`, `while`, `mut`, `until`, `Type`, `Prop`, `bif`,
`dbg_trace`, ...). Re-run it when the toolchain moves; it fails loudly and
refuses a vacuous (empty) token table. Test: `test_keywords.lem` (B5
section: locals and a top-level `matches`).

## B6. Parenthesised binder parameters (fixed)

`let analysed_locations_at_pc (ev) (ds: dwarf_static) ...` rendered `(ev)`
as `((ev : T))` ("expected '_' or identifier"); likewise `((z))` and `(_)`.
In parameter position, source parentheses around a pattern that already
renders as a parenthesised binder (variable, wildcard, typed pattern,
annotated variable, unit) are dropped. Test: `test_patterns.lem` (B6
section).

## B7. Mutual-record literals emitted in the wrong order (fixed; silent miscompile class)

Records in a mutual block are emitted as single-constructor inductives and
their literals as positional `T.mk v1 v2 ...`. The values were emitted in
the order the LITERAL lists its fields, not the declaration order. linksem's
`sdt_subroutine` literal lists `ss_unspecified_parameters` before
`ss_pc_ranges`: a type error there, but wherever the swapped fields share a
type it compiles and silently exchanges them. Fixed: values are placed by
the type's declared field list, matched by field descriptor; a literal
that does not give every field exactly once is refused. (Record update
already used the declared list.) Test: `test_mutual_record_order.lem` (two
`nat` fields swapped in the literal; every field asserted).

## B8. `fail` and closed-term extraction (fixed)

LemLib's `Lem_Assert_extra.fail {a} [Inhabited a] : a := failwithI "fail"`
is an ordinary definition: every use `@fail Char inst` is a closed term,
which Lean 4.28 hoists into a module initialiser. linksem's
`hex_char_of_nibble` ends in `else fail`, so every program importing
`missing_pervasives` panicked at START-UP. Panic messages are disabled
during initialisation, so the symptom under `LEAN_ABORT_ON_PANIC=1` was a
silent SIGABRT (exit 134, no output); without it, the run looked normal.
Localised with one probe executable per module (`import M; def main :=
pure ()`) and the generated C of the initialiser. Fix: a polymorphic
definition with no explicit parameters and a non-function type is emitted
`@[never_extract]` (as `failwithI` itself is). Test:
`test_untaken_failure.lem` / `lean-untaken-failure` (`pick_char`).

On Lean 4.32.2 (review fix 2026-09-30, LOW e), closed terms are
initialised lazily, so leg 1 no longer tells the difference: without the
attribute it passes too. The attribute still matters, and leg 4 now tests
it. Leg 4 reaches `Assert_extra.fail` at two different runtime arguments
without `LEAN_ABORT_ON_PANIC`. With `never_extract`, each reached failure
panics, and OCaml raises each time. Without it, `@fail Char _` is
extracted and initialised ONCE, and the second failure is silent. That
was measured in a scratch package: `pickB` without the attribute printed
one PANIC for two failing calls, and `pickA` with it printed two.
Plant-tested on the suite: see the review-fix section.

## B9. Closed calls in untaken branches evaluated at load (fixed; toolchain-dependent)

B8 is one case of a general hazard: on Lean 4.28 ANY closed application of
a partial function, anywhere in a function body, is hoisted and evaluated
when the module loads. Probe: `def f (b : Bool) := if b then g 10 else 0`
with `g 10` a `failwithI` aborts at start-up although the branch is never
taken; the OCaml target evaluates it only when reached. The existing
`TestFailwithThreadingPanic.lean` comment records the same effect in
LemLib's own modules as a "toolchain caveat (4.28)" and notes that on
≥ 4.32 closed terms are initialised lazily. Fix: generated modules are
compiled with `set_option compiler.extract_closed false` (emitted after the
imports): strict, in-place evaluation, as in OCaml, on every toolchain.
Top-level constants are unaffected (initialised at load on both targets).
Cost: closed subterms are recomputed per evaluation instead of cached;
measured on linksem in the record's timing section. Test:
`lean-untaken-failure` (leg 1: untaken branches, exit 0 under
`LEAN_ABORT_ON_PANIC=1`; leg 2: the taken branch fail-stops with its
message).

## B10. Reserved-name lists loaded fail-open (fixed; upstream Lem)

`Initial_env.read_target_constants` wrapped the load of
`library/<target>_constants` in `try ... with _ -> NameSet.empty`: any failure
to read the file silently disabled the renaming pass for that target. For
Lean that means unescaped keywords (`from`, `by`), constructors ambiguous
with the root namespace (`One`, `Add`, `Seq`) and class names colliding with
Lean's (`Ord`): broken output, no diagnostic. It happened for real (B12):
seven parity probes failed to compile in one suite run with exactly those
errors. Targets that ship a constants file (ocaml, hol, isabelle, coq, lean)
now fail loudly if it is missing or unreadable; tex/html/lem (no file by
design) keep the empty set. Output is unchanged whenever the file reads.
Test: `lean-constants-required` (plant: a library copy without
`lean_constants` is refused; the intact library generates).

## B11. Local lambda lets with destructuring parameters (fixed)

linksem's `link.lem` binds `let apply_reloc = fun img -> fun (el_name, start,
len) -> fun s -> fun a -> ...`. Lem's pattern compiler makes the tuple
parameter a `match p with | (el_name, start, len) => fun ...`; with no
expected type Lean infers a DEPENDENT motive, and the local function gets a
type like `?m img p` that cannot be applied ("Function expected"). A local
`let x = fun ...` without an annotation is now annotated with the
right-hand side's Lem type. Test: `test_lambda_let.lem` (monomorphic, and
inside a polymorphic definition).

## B12. Relative `LEMLIB` exported by the suite Makefile (fixed; harness)

`tests/comprehensive/Makefile` set `LEMLIB = ../../library`. If `LEMLIB` is
set in the caller's environment (lem's own docs suggest it), make exports
the Makefile's value to every recipe, and the relative path is wrong for
recipes that change directory (`parity/run.sh`): before B10 the parity
probes then silently compiled with no reserved-name list; after B10 the
admission test failed loudly. Now `$(abspath ../../library)`.

## B13. Lem `if` emitted as Lean `if` got stuck in context (fixed; was L1)

linksem's `link.lem` (`mark_fate_of_relocs`) failed with "Application type
mismatch: `binding_is_final options b` has type Bool but is expected to have
type Prop in `@ite ...`". Root cause, from a `trace.Meta.synthInstance` run
on a delta-debugged reduction (12k -> 2k characters, every step re-checked
for the same error): Lean's `if c then t else e` expands to `let_mvar% ?m :=
c; wait_if_type_mvar% ?m; ite ?m t e`; for a Bool `c` the elaborator must
solve the coercion problem `CoeT Bool c Prop` (whose goal CONTAINS the term
`c`) and then `Decidable ?m`. Here `c` mentioned a let-variable whose value
still carried a postponed `match`, the coercion problem failed with an
internal stuck exception, `Decidable ?m` stayed unsolved, and `ite` was typed
with the uncoerced Bool. Standalone reproduction (plain Lean, no Lem): a
`List.foldl` lambda with tuple matches, a let-bound typed lambda whose body
matches on an `Option`, a value from a polymorphic helper with instance
arguments, a destructuring `match` on it, then `if f x b then ...`.

Every Lem `if` has a `bool` condition, so the backend now emits LemLib's
`lem_if c then t else e`, which expands to `@ite _ (c = true)
(instDecidableEqBool _ _) t e`: no coercion and no instance search (the
instance's arguments are solved by unification), the condition written
once, and the SAME kernel term Lean elaborates for a Bool `if` (checked on
the elaborated definitions in `LemLibTest`, plant-tested with a `cond`
expansion), so proofs over generated code are unaffected. Caveat, stated
exactly: the identity holds when the RENDERED condition is a Bool, which it
is for every live conditional in LemLib, linksem and the tests (checked: the
only Prop-rendered conditions are in commented-out bodies of definitions
with target reps); a condition whose Lean target rep produced a Prop would
elaborate as `decide p = true`: same behaviour, not the same term. Prop contexts
(indreln premises, `St.prop_equality`) keep the builtin `if`. `lem_if` is a
token, reserved in both avoid lists. With it the whole linksem model
compiles, `Link.lean` included (214 jobs). Test: `test_if_bool_cond.lem`
(the linksem shape in Lem; plant: pristine c2a68e7 output fails to compile
with the original error, this branch compiles and its assert passes).

## B14. Instances at several tuple arities resolved by Lean, not Lem (fixed)

Found by the `main_link` lane (2026-09-29). Lem tuples are n-ary; Lean's
are right-nested pairs, so the Lean type of a Lem triple whose LAST
component is a pair, `a × b × (c × d)`, IS the Lean type of a quadruple.
A class with instances at several tuple arities (linksem's `Show`: pair,
triple, quad) therefore has overlapping Lean instances at such a type, and
Lean picks the most recently declared one: `(1, 2, (3, 4))` showed as
`(1, 2, 3, 4)`, a pair `(1, (2, 3))` as a triple. Lem inlines a method at a
known instance (so the top-level choice was right in generated code); the
wrong choice was in the instance ARGUMENTS Lean re-resolves (a list of such
triples, a generic caller, a nested pair) and in hand-written Lean calling
the class method (linksem's `main_link` driver, since fixed to call what
Lem resolves to). Fix: non-default tuple instances get a global name
(`lemInst_[Lem_]<module>_Instance_<class>_<type>`, `Lem_` for library
modules, since linksem's `Show` and LemLib's `Show` both have a pair
instance); a use of a constant whose class constraints reach a confusable
tuple type (Lem's own resolution, `get_matching_instance`) binds exactly
Lem's instances locally, innermost first (`haveI := lemInst_... (a := T1)
...; e`); Lean's local instances take precedence over global ones.
Exempt: Basic_classes' `Eq`/`Ord`/`SetType`/`MapKeyType` (their tuple
instances are componentwise / lexicographic, so the overlap computes the
same result). The walk over instance constraints is bounded at depth 50,
and past the bound it refuses loudly (review fix 2026-09-30, LOW a). It
used to stop silently, which would have left demands unbound. Lem's
constraints are normally on component types, so real chains are short.
The bound is a bound, not a proof: a legitimate chain deeper than 50 would
also be refused, loudly (no case near it is known). Since review round 2,
the error carries the source position of the constant use. The supply-threaded paths refuse such a use (loud). Test:
`test_tuple_inst_arity.lem` (7 asserts; with the bindings stripped, 3
fail: nested, list, generic). LemLib: one instance renamed
(`Lem_Show` pair). linksem: instance names only (no confusable use in the
model).

## B15. `let _ = e1 in e2` dropped e1 (fixed)

Found by the `main_link` lane (a model diagnostic missing on stderr). Lem's
sequencing idiom evaluates e1 for its effect; OCaml is strict, so e1 runs
and a failure in e1 stops the program. Lean's compiler drops an unused pure
`let`, and treats any `Unit` value as `()` (even `match e1 with | () => e2`
and an opaque `implemented_by` consumer of the value were removed): the
model's `errln` diagnostics vanished and, worse, a FAILING e1 was skipped
(fail-open). Fix: `let _ = e1 in e2`, `let () = e1 in e2` (which reaches
the backend as a one-arm match) and one-arm matches on `_`/`()` are emitted
as `lemSeq (fun _ => e1) (fun _ => e2)`. LemLib's `lemSeq` is logically
`e2` (`b ()`); its `implemented_by` body forces e1 by storing the value in
a fresh `IO.Ref` (a `BaseIO` effect the compiler keeps; a pure "use",
`if ptrAddrUnsafe x == 1 then b () else b ()`, was simplified away and
arity reduction then dropped the argument). A variable or literal e1 keeps
the plain emission (no effect possible). The supply-threaded paths refuse
a pure e1 (loud). Cerberus's hand-written
`print_debug_pure : Nat → List d → ...` is more general than Lem's
`list domain`, so `lemSeq (fun _ => print_debug_pure 2 [] ...)` leaves `d`
unsolved. (The old `match e1 with | () => e2` elaborated only because Lean
discards the discriminant of a `()` pattern: e1 was already dropped in the
elaborated term.) B15 first ascribed an empty list literal of closed Lem
type only inside a discarded e1. Since the review fix of 2026-09-30
(LOW c), EVERY empty list literal whose Lem type is closed is ascribed
(`([] : List T)`), wherever it occurs. The hazard is not specific to
discarded e1: `let y = f [] in y + n`, with `f` a `List.length` rep of a
`list bool -> nat`, failed to elaborate with "don't know how to
synthesize implicit argument `α`" under the old rule. The reviewer's
alternative, ascribing the whole discarded e1 with its Lem type, was
measured and does not help: e1's type, `nat` or `unit`, does not mention
the unsolved parameter. The ascription only affects elaboration; the
kernel term is the same `@List.nil T`. Test:
`test_empty_list_ascription.lem` (discarded, used `let`, nested unit `let`,
inside a `match`). LemLib's generated modules gain the ascriptions (List,
String_extra, Word). Other nullary polymorphic values (`Nothing`, empty
sets and maps) passed to an over-general rep are exposed to the same
elaboration failure. That failure is loud (a Lean build error), and none
is known in Cerberus or linksem.

Residual, precisely (review round 2, LOW-1): the rule covers only CLOSED
element types. An empty list whose Lem type mentions the enclosing
definition's type variables (`list 'a` inside
`let bound_use (x : 'a) = ...`), passed to a rep more general than its Lem
type in a position that does not fix the element type, still fails to
elaborate, loudly. Extending the rule to such types is not sound as
emitted today, so it was not done. The backend renames a PARAMETER that
collides with a type variable (`{a : Type} (a1 : Nat)`) but not a LOCAL
binder. In `let shadow2 (xs : list 'a) : nat = let a = 3 in a +
List.length (match xs with [] -> [] | y :: ys -> ys end)`, the local
`a := 3` shadows the type binder `a`. Hand-ascribing that `[]` as
`([] : List a)` makes a definition that compiles today fail ("failed to
synthesize instance of type class OfNat (Type ?u.16) 3", measured).
Extending the rule would first need local binders renamed away from the
type variables in scope. The Cerberus tree was NOT regenerated
with this rule; the re-pin must check it. Tests: parity
failure probes `f_let_seq.lem`, `f_let_unit.lem` (OCaml and Lean both fail
with the discarded e1's message; pre-fix the Lean binary printed the next
step and exited 0).

Cerberus impact of B15: 266 sites (its `print_debug_pure`/`warn` debug
calls, no-ops in its Lean twins, so no behaviour change). Two hand-written
proofs unfold definitions through these sites and need `lemSeq` in their
`simp only` sets (`Core_run_aux_lemMeasureProofs.lean`,
`Driver_lemMeasureProofs.lean`: one word each; verified in the scratch
clone, 395 jobs build). This is an edit for the Cerberus re-pin, not made
in the Cerberus checkout.

Cerberus behaviour with A1 + B14 + B15 (scratch clone, csmith corpus lane,
`scripts/measure_csmith_cpu.py --max 200`): 97 match, 102 CERB_SKIP, 1
timeout, 0 baseline regressions after A1 and again after B14/B15 (the same
statuses as before A1). Lean CPU over the 97 matched inputs: 34.82 s (A1),
32.58 s (B14/B15); the unchanged OCaml oracle moved by the same order
(14.34 s, 13.17 s), so no measurable cost.

## B15b. `let x = e1 in e2` with `x` unused dropped e1 (fixed)

The general case of B15, found while reviewing it: OCaml evaluates the
right-hand side of every `let` (strict), so a failing e1 stops the program
even when its value is never used; Lean's compiler drops an unused binding.
linksem had 58 such sites, some of which fail (e.g. the linker's
`match got_el.startpos with Just a -> a | Nothing -> failwith ...` bound to
an unused name). A `let` whose pattern cannot fail to match (variables,
wildcards, tuples of them, parentheses, annotations) and none of whose
variables is free in the body is now emitted as `lemSeq` like `let _ =`;
the supply-threaded path refuses a pure e1 (loud). Test: parity failure
probe `f_let_unused.lem` (plus an in-domain tuple step). Cerberus: 2 sites
(pure, non-failing), tree compiles; csmith lane statuses unchanged (97
match / 102 skip / 1 timeout, 0 regressions). The general hazard remains for
unused ARGUMENTS after inlining (`const x (failwith ..)`): Lean may drop
the failing argument where OCaml evaluates it (audit A3 family,
documented).

## Impact on the Cerberus tree (measured, not re-pinned)

Generated with this branch (lem `65389aa`) in a scratch clone of cerberus-lean
`d62f52121` (the container checkout untouched): 170 files; differences from
c2a68e7 output are B4 expansions, B8 attributes (9), B9's option (170 files),
B11 annotations (~120) and B13 `lem_if` (414). No `.mk` literal reorderings
(B7 does not affect Cerberus). The tree COMPILES (395 jobs, Lean 4.32.2,
LemLib from this branch by path).

B9 cost, A/B on that one tree (only difference: the `set_option` lines in
the 170 modules and LemLib's generated modules), csmith corpus lane via
`scripts/measure_csmith_cpu.py --max 200` (CPU = user+sys, GNU time):
- Lean CPU over the 97 inputs Lean ran and matched in both: A (extraction
  on) 32.61 s, B (B9) 39.45 s: +21.0 %; per input over the 10 inputs with
  >= 0.5 s: median +12.6 %, range +2.3 % .. +73.2 % (sa_csmith_272:
  5.38 s -> 9.32 s); max RSS +4.2 %.
- control, the unchanged OCaml oracle binary: B/A = 0.992 (the load moved
  between 3.7 and 58 across the runs; CPU is comparable to ~1 %).
- lane statuses identical in both variants.

Toolchain check of the hazard B9 removes (`if b then g 10 else 0`, `g 10`
panicking, run with `LEAN_ABORT_ON_PANIC=1` and no arguments): Lean 4.28.0
aborts at start-up (exit 134); Lean 4.32.2 exits 0 (closed terms are
initialised lazily at first use), and still aborts when the branch is taken.
So B9 is required on LemLib's pinned 4.28.0 and buys nothing on 4.32.2,
where it costs ~21 % CPU on this lane. Options (operator decision): keep B9
unconditional; or move lem-lean's toolchain pin to 4.32.2 (Cerberus's) and
drop the option, keeping `lean-untaken-failure` as the guard that fails if a
toolchain with eager closed-term initialisation comes back.

## Toolchain move to Lean 4.32.2; B9 retired (2026-09-29)

[USER 2026-09-29] agreed: move lem-lean's pin to Lean 4.32.2 (Cerberus's
toolchain; on the roadmap) and drop B9. All five `lean-toolchain` files now
pin 4.32.2; generated modules no longer set `compiler.extract_closed false`
(the backend comment at the former emission site records why); B8
(`never_extract` on nullary polymorphic definitions) stays; the
`lean-untaken-failure` target is now the guard of lazy closed-term
initialisation and passes on 4.32.2 without the option. The keyword probe
found 12 identifier-shaped core tokens new in 4.32.2 (`cbv_eval`,
`cbv_simproc`, `idbg`, `inferInstanceAs`, `unlock_limits`, ...); they were
added to both avoid lists.

## Audit follow-up (2026-09-29)

Five independent auditors compared the Lean port of linksem with the OCaml
build; the linksem record lists every item. Backend-side:

- **A2. Panics continued by default (fixed).** A reached `failwithI` is a
  Lean `panic!`. Unless `LEAN_ABORT_ON_PANIC=1` is set, it prints and
  CONTINUES with the `Inhabited` default. An executable over generated code
  could then exit 0 with plausible output where the OCaml target raises
  (linksem: invalid program-header flags printed a table with an empty
  column). The first fix, `lemFailStop` over an
  `@[extern "lean_internal_set_exit_on_panic"]` opaque `lemSetExitOnPanic`,
  was REMOVED by ruling D1(b) [USER 2026-09-30] (see "Native seams"
  below). LemLib now provides `lemRequireAbortOnPanic : IO Unit`, with no
  extern and no unsafe code. A client calls it first in `main`. It reads
  `LEAN_ABORT_ON_PANIC` with `IO.getEnv`, and unless the value is exactly
  `1` it prints an attributed refusal on stderr and exits 2. This is the
  pattern of Cerberus's driver (`lean_frontend/Main.lean`, Z2-FL-03). That
  driver measured that the runtime aborts when the variable is merely
  present, so the check here is stricter than the runtime. Tests:
  `lean-untaken-failure` legs 3a (unset: refused, exit 2, nothing run),
  3b (`0`: refused) and 3c (`1`: passes, and the reached failure
  fail-stops). Plant: see the review-fix section.
- **A3. Failures inside function-returning definitions fire later (documented
  limitation).** Lean's compiler eta-expands every definition to the arity of
  its TYPE (`Lean/Compiler/LCNF/ToDecl.lean:155`, `Meta.etaExpand`, no
  opt-out short of `@[extern]`/`@[init]`), so for `f (x) : A -> B := if c
  then g else failwith ..` the body runs when the returned function is
  applied, whereas OCaml runs it when `f` is applied to `x`. Only the timing
  of failures (and non-termination) differs; the outcome flips only if a
  failing function value is built and never applied. linksem reaches it with
  an unknown DWARF attribute form (both sides fail, different messages).
  Matching OCaml would need a non-function wrapper type for every such
  definition and its uses; not taken.
- **A4. Evaluation order (documented limitation, existing).** OCaml
  evaluates arguments right to left, Lean left to right. With two failing
  subexpressions, the reported failure differs and both fail. The order
  can also change the OUTCOME. If one argument fails and another does not
  terminate, the target that evaluates the failing one first fails, and
  the other target does not terminate. So a failure on one target can be
  non-termination on the other (in either direction).
- **A5. A `let` floated into an untaken branch or a closure (OPEN, review
  finding HIGH-2, 2026-09-30).** Take `let x = e1 in e2` where `x` IS
  free in e2, but only in a branch that is not taken, or only inside a
  local closure that is never called. OCaml is strict: it evaluates e1 at
  the `let`, so a failing e1 stops the program. Lean's compiler floats the
  binding to its use (LCNF let-floating into the branch, and into the
  closure), so e1 never runs and the program continues. B15b covers only
  bindings whose variable is not free in e2 at all. Probes, both
  registered in `parity/expected_failures.txt` (class 3, open), each run
  with the runtime `n = 0`:
  - `f_let_float_branch`:
    `let x = checked_pred n in if n = 7 then "used: " ^ show x else "after ..."`;
  - `f_let_float_closure`: `x` used only in
    `let g = fun (u : unit) -> "used: " ^ show x in if n = 7 then g () else "after ..."`.
  In both, OCaml fails with `Failure("let_float_…: e1 failed")` after
  `before: 0`, and the Lean binary prints `after (must not print): 0` and
  exits 0. It is the same family as A3 and B15b: Lean's compiler is free
  to move or drop pure computation, and a Lem failure is pure in the
  logic. Fix options, NOT implemented (an operator decision on cost):
  1. **A strict `lemLet e1 (fun x => e2)`** for every `let` with a
     non-trivial e1. Its implementation forces e1 before calling the body
     (the `lemSeq` mechanism with the value passed on). This adds a native
     seam with the same kernel-versus-runtime gap as `lemSeq`, so it needs
     a boundary ruling. Every `let` in generated code becomes an
     application: proofs that use `zeta`/`simp only [...]` through lets
     need `lemLet` in their simp sets, as B15 needed `lemSeq` in two
     Cerberus proofs. It also stops let-floating and allocates a closure
     per `let` body. The CPU cost is unmeasured, and B9's 21 % on
     Cerberus is the order of magnitude to expect for a blanket change.
  2. **The same, restricted to lets whose variable is not used on EVERY
     path** (a use analysis). The cost is lower, but every precision hole
     in the analysis is a silent discrepancy. Closures and inlining make
     "used on every path" hard to decide conservatively.
  3. **`let x := e1; lemSeq (fun _ => x) (fun _ => e2)`**: reuse the
     existing (temporary) seam to force `x`. No new seam, but it has the
     proof and speed costs of option 1, and it rests on a seam whose mover
     (below) would delete it.
  4. **The failure-monad translation** (TODO item 24, D1(a)'s named
     mover) fixes it structurally, with A3 and A4. It is an L-sized arc,
     with a design pass first.
  5. **A documented limitation**, like A3.
- **A1. Comparison residuals (confirmed, fixed).** Lem's default `Eq` /
  `SetType` / `MapKeyType` instances are OCaml's polymorphic compare, valid
  at every type. The backend's comparisons at a type with a type variable
  that carried no Lem constraint resolved to priority-50 fallback instances
  whose methods panicked (~200 sites in linksem). Because of A2 the
  panic returned a default value: sets kept duplicates (`tag_image` twice:
  OCaml 2 tags, Lean 3), and the Lean linker built an executable with entry
  point 0 and no `.text`. Types with function-typed fields
  (`amd64_abi_feature`) panicked on EVERY comparison, not only when a
  closure is reached. Fix (design:
  `doc/notes/2026-09-29_comparison-dictionaries-design.md`): Lem-instance-guided
  threading of `[Ord a]`/`[BEq a]` binders (transitive, fixpoint);
  function-typed positions are compared structurally with
  `lemFunctionalCompare`/`lemFunctionalBeq`, which fail with OCaml's
  message `compare: functional value` whenever they reach a closure. That
  matches OCaml's `=`, which raises on any closure it reaches. It does NOT
  match OCaml's `compare` (see A1-R below). The fallback instances are
  DELETED, so any missed demand is a compile error. Tests: `test_cmp_threading.lem` (the
  pristine output fails 3 of 4 asserts), `test_fn_field_compare.lem`.
  linksem: no fallback left; one loud residual remains
  (`allocated_sections_map`, a map over a mutual sibling, never compared).
  Cerberus (scratch clone `d62f52121`, container checkout untouched): 23
  generated files change (729 fallback-instance lines deleted, threaded
  binders, derived comparisons for function-field types such as
  `pre_execution`); the tree compiles (395 jobs) against this LemLib.
- **A1-R. Residual discrepancy: `compare` on the same closure (OPEN,
  review finding MEDIUM-1, 2026-09-30).** OCaml's polymorphic `compare`
  returns 0 for two occurrences of the SAME closure object: it checks
  physical equality first. It raises only for DISTINCT closures. Only `=`
  raises on every closure. Measured with a native OCaml binary:
  `compare f f = 0`, `f = f` raises `Invalid_argument "compare: functional
  value"`, `compare f g` raises, and `compare [f] [f]` on fresh lists is
  0. LemLib's `lemFunctionalCompare` fails on every closure. So a set of
  function-field values sharing one closure computes on OCaml and fails on
  Lean. Probe `p_fn_compare_same_closure`:
  `Set.size (Set.fromList [GOT [f]; GOT [f]; Plain 1])` is `size: 2` on
  OCaml, and Lean aborts with
  `PANIC at _private.LemLib.0.failwithIImpl LemLib:239:2: compare: functional value`.
  It is registered in `parity/expected_failures.txt` (class 3, open). The
  parity runner now admits a Lean panic abort (exit 134 after a
  `PANIC at` line) where OCaml succeeded as a real disagreement for such
  entries. Plant: with the PANIC match disabled, the probe is red,
  "not XFAIL". Fix options: (1) a pointer-equality test before failing
  (`ptrAddrUnsafe`, i.e. a new native seam). Not taken, per the brief: it
  needs a boundary ruling, and it would make logical equality depend on
  sharing. (2) Rule it an OCaml-target deviation (behaviour that depends
  on sharing is not a semantics). The decision is the operator's.
- **Comparison at a function type is refused at Lean compile time.** A
  threaded binder demanded at a function type fails instance synthesis
  (review finding LOW f, measured). Example: `tags_of : list (tag 'a) ->
  set (tag 'a)` used at `tag (nat -> nat)`. Lem generation succeeds; Lean
  reports `failed to synthesize instance of type class Ord (Nat → Nat)`.
  OCaml compiles it and raises only if a comparison reaches a closure:
  `tags_of [NoTag; NoTag]` computes a set of size 1. This is loud (a build
  error, not a wrong answer), but a valid Lem program the Lean target
  cannot compile. Recorded as a limitation. Matching OCaml would need an
  `Ord` for function types that fails when used, which is the deleted
  fallback-instance shape.

## Native seams: boundary rulings (2026-09-30)

A native seam is an `@[implemented_by]` body (or an `@[extern]`) whose
run-time behaviour is not the logical definition the kernel sees. The
orchestrator relayed the operator's rulings: D1 [USER
2026-09-30] agreed; D2 [USER 2026-09-30] agreed. Each was
given on the orchestrator's recommendation, which is paraphrased below
and is not the operator's words.

- **`lemSeqImpl`, behind `lemSeq` (B15/B15b).** `lemSeq {α β} (a : Unit →
  α) (b : Unit → β) : β := b ()` is a transparent definition: the kernel
  and every proof see `b ()`. Its `implemented_by lemSeqImpl` forces `a ()`
  at run time first, by storing the value in a fresh `IO.Ref` under
  `unsafeBaseIO`, and then returns `b ()`. The gap: a failure or
  non-termination in `a` is visible at run time and invisible to the
  logic. That is the intent (it mirrors OCaml's strict `let`), but it is
  a trust boundary. It is also an exception to LemLib's L2 note "DO NOT
  REINTRODUCE an axiom or unsafe effect-projection". **Ruling D1(a):
  ACCEPTED onto the boundary list as TEMPORARY, not permanent.** Its named
  mover is the failure-monad translation (TODO item 24): an effect
  analysis in the backend emits every function that can transitively
  reach `failwith` in an error monad (`Except`), so strictness and
  evaluation order become part of the semantics. That fixes the `lemSeq`
  gap, A5, most of A3, and lets A4 follow OCaml's order. The TODO entry
  says: queued, design pass with the operator first.
- **`lemSetExitOnPanic` / `lemFailStop` (A2's first fix).** This was an
  `@[extern "lean_internal_set_exit_on_panic"]` opaque, `BaseIO Unit`: a
  call into a runtime-internal symbol, with no logical content.
  **Ruling D1(b): REMOVED from LemLib.** It is replaced by the unsafe-free,
  extern-free check `lemRequireAbortOnPanic : IO Unit` (A2 above).
  `lean-untaken-failure` leg 3 was updated, and plant-tested: removing the
  call from the leg's driver makes the leg fail.
- **LemLib's native-seam population after D1** is exactly
  `failwithIImpl` and `fuelExhaustedWithImpl` (permanent, the loud-failure
  primitives), plus `lemSeqImpl` (TEMPORARY, D1(a)). LemLib has no
  `@[extern]`. Checked on this branch: a grep for `@[extern` and
  `implemented_by` over `lean-lib/**/*.lean` finds exactly these three
  attribute uses, and nothing else outside comments.
- **LP4's semantics conflict** (library-parity record LP4; ACCEPTED on
  2026-09-30 as a ruled OCaml-target deviation, see below): Lean's reps
  are unbounded, OCaml's are 63-bit and wrap, and HOL/Isabelle/Coq use
  Lem's 31-bit definition. **Ruling D2** accepted LP4 SUBJECT TO a
  measurement that the OCaml reps are unbounded. The measurement
  (`p_word_bitwise_wide`) shows they WRAP at 63 bits, so the condition is
  not met and LP4 went back to the operator. **Ruling, 2026-09-30:**
  [USER 2026-09-30] agreed on points 1-3 of the orchestrator's questions and approved proceeding: (1) accept LP4 and OM4 as
  registered OCaml-target deviations under the 2026-09-03 X3 ruling
  ([USER 2026-09-03]: OCaml limits hardcoded because of OCaml-level execution issues are forbidden as well; the logical semantics is what counts) and (2) keep the `p_word_bitwise_wide_mul` runner
  row, and (3) a fresh delta review of round 2 before landing (done:
  review round 3, below). LP4 and OM4 are ACCEPTED; `p_word_bitwise_wide`
  and `p_mword_width` are class `ruled`. The verbatim diff and the upstream-Lem candidate (the
  width-limited prover definitions) are in the library-parity record.

## Review fixes (2026-09-30)

Two independent reviews of `arc/linksem` at `66e3cf8`. The worker is
[AGENT]; findings marked "confirmed" were confirmed by the orchestrator.

- MEDIUM-3 (confirmed): the missing record
  `2026-09-30_library-parity-coverage.md` is committed, scoped to this
  branch (see its §0 for what was cut and where it lives).
- HIGH-2: recorded as A5, OPEN, with two XFAIL probes.
- MEDIUM-1: A1's wording is corrected here and in
  `doc/notes/2026-09-29_comparison-dictionaries-design.md`. Recorded as
  A1-R, OPEN, with one XFAIL probe.
- LOW a: the B14 depth bound is loud (B14).
- LOW b: `scripts/lean_keyword_probe.sh` re-executes itself once under
  `scripts/capped`, so the whole batch is one capped job
  (`CERB_MEM_MAX`, default 32G). Checked: with `CERB_MEM_MAX=bogus`, the
  cap wrapper rejects the value and the probe exits 2. The token dump's
  `2>/dev/null` was dropped.
- LOW c: the empty-list ascription is a context-free rule (B15).
- LOW d: the new LemLib root names (`lemChr`, `lemFunctionalBeq`,
  `lemFunctionalCompare`, `lemIntAsr`, `lemIntLand`, `lemIntLor`,
  `lemIntLsl`, `lemIntLxor`, `lemNatAsr`, `lemNatLand`, `lemNatLnot`,
  `lemNatLor`, `lemNatLsl`, `lemNatLsr`, `lemNatLxor`,
  `lemRequireAbortOnPanic`, `lemSeq`) are in `library/lean_constants`.
  Test: `test_keywords.lem`, where user definitions of six of these names
  are renamed and asserted. That list was found by diffing LemLib's
  top-level declarations against `c2a68e7`. Open, not done: LemLib's
  OLDER root names (`failwithI`, `fuelExhausted`, `lemIntDiv`, …) are not
  in the file either. Only `LemFuel` and `lem_if` were. A Lem user
  definition with one of those names would collide. This gap predates
  this branch.
- LOW e: B8 is discriminated again on 4.32.2 (B8, leg 4).
- Plants for legs 3 and 4 (`make lean-untaken-failure`), verbatim verdict
  lines. First, the `lemRequireAbortOnPanic` call replaced by `pure ()`
  in the driver:
  `FAIL (leg 3a): lemRequireAbortOnPanic with LEAN_ABORT_ON_PANIC unset did not refuse before running: exit 0: PANIC at _private.LemLib.0.failwithIImpl LemLib:239:2: must_be_small: too big`.
  Second, `@[never_extract]` removed from the generated
  `LemLib/Assert_extra.lean` `fail`:
  `FAIL (leg 4): expected 2 PANIC lines (one per reached Assert_extra.fail, B8 never_extract), got 1, exit 0: PANIC at _private.LemLib.0.failwithIImpl LemLib:239:2: fail`.
  Both were restored, and a rebuild gave `OK (leg 3a)` … `OK (leg 4)`.
- Suite vacuity hazard (found while gating, not fixed): the suite
  generates every `test_*.lem`, but it COMPILES (and runs the asserts of)
  only the modules listed as roots in `tests/comprehensive/lean-test/lakefile.lean`.
  `test_empty_list_ascription` was generated and green before it was
  added as a root, so its asserts had not run. It is a root now, and every
  other `test_*.lem` was checked to be one. Nothing forces this; a check
  in `lean-compile` that each generated `Test_*` module is a root would.
- LOW f: comparison at a function type is refused at Lean compile time
  (under A1).
- LOW g: A4's wording now covers failure versus non-termination.
- Parity runner: `expected_failures.txt` gained class (3), an OPEN
  discrepancy awaiting an operator decision [AGENT, on the orchestrator's
  instruction to register open discrepancies as XFAIL]. The runner now
  also treats a Lean panic abort (exit 134 after a `PANIC at` line) on a
  non-failure probe, where OCaml succeeded, as a real parity
  disagreement. Any other crash stays red.

### Migration note: `lemFailStop` removed (API break)

`lemFailStop` and `lemSetExitOnPanic` are gone from LemLib (ruling D1(b)).
An external client that called them no longer builds; linksem's Lean
drivers `MainElf.lean` and `MainLink.lean` are known to. Migration:
replace the call `lemFailStop` (a `BaseIO Unit`) with
`lemRequireAbortOnPanic` (an `IO Unit`), still first in `main`, and run
the executable with `LEAN_ABORT_ON_PANIC=1`. Without the variable the
program now REFUSES to start (exit 2) instead of switching exit-on-panic
on by itself. lem-lean has no changelog file; this note, and a pointer in
`doc/lean-backend/README.md`, carry the break.

## Review round 2 (2026-09-30)

An independent delta review of `66e3cf8..2ea67cf`. The worker is [AGENT].

- MEDIUM-1 (confirmed by the reviewer's plants): a registered probe
  absorbed ANY new disagreement, because the Lean side was never pinned.
  Now every registered probe has `expected/<probe>.lean.out`: the Lean exit
  status, stdout and (failure probes) stderr, with backtrace lines and
  the shell's "Aborted (core dumped)" removed and PANIC positions masked.
  XFAIL requires an exact match; any other difference is
  "FAIL: registered probe's disagreement CHANGED". Rebaselining is explicit
  (`REBASELINE_XFAIL=1`). Plants, all red:
  - A: `lemIntLsl` planted wrong at n = 61, so the agreeing control row of
    `p_word_bitwise_wide` changes on the Lean side:
    `< control intLsl 1 61 = 2305843009213693952` / `> control intLsl 1 61 = 0`.
  - B: `lemFunctionalCompare`'s message planted, an unrelated panic in
    `p_fn_compare_same_closure`:
    `< PANIC at _private.LemLib.0.failwithIImpl LemLib:<pos>: compare: functional value` /
    `> PANIC at _private.LemLib.0.failwithIImpl LemLib:<pos>: PLANTED unrelated panic`.
  - C (worker's own): the untaken-branch text of `f_let_float_branch`
    changed; OCaml's prefix is unaffected: `< after (must not print): 0` /
    `> after (PLANTED): 0`.
  - D: `test_failure_admission.sh` (planted compiler failure) stays red:
    "OK (registered probe with compiler failure is red, not XFAIL)".
  - E: a registered probe that passes (`p_hello`, with a Lean pin):
    "FAIL: EXPECTED FAILURE NOW PASSES".
  All planted files were restored.
- LOW-4: `expected_failures.txt` entries are now `<probe>,<class>,<reason>`
  with class `fix`, `ruled` or `open`. Before any probe runs, the runner
  rejects a malformed line, an unknown class, a duplicate, an orphan entry
  (no such probe), a registered probe without a Lean pin, and an orphan Lean
  pin. The unused `xfail_status` is replaced by counters and a summary line
  (`parity: N probes: k OK, x XFAIL (registered, Lean side pinned), f FAIL`).
  Plants, all refused: unknown class (`line 25: unknown class "maybe"`),
  orphan entry, missing Lean pin, orphan Lean pin, malformed line,
  duplicate (`line 28: duplicate entry for p_mword_width`), and a crashing
  validator (a fake `awk` exiting 3: "the registry validator itself
  failed (awk exit 3) — refusing to run"). The plants found a real bug in
  the first version: the awk validator used the gawk builtin name `exp`,
  crashed, and its failure was ignored, so an invalid registry passed.
  The validator's exit status is now checked.
- MEDIUM-2: LP4 is relabelled "implemented; acceptance OPEN (D2 condition
  not met)" in both records and in the LemLib/LemLibTest comments.
  `p_word_bitwise_wide` now isolates the bitwise operations (operands are
  literals or `lsl` results), and the multiplication-built rows are
  `p_word_bitwise_wide_mul` (class `ruled`, X3/N4).
- LOW-3: `lnot` at `nat` was a false claim of the round-1 record (not
  measured). It is unreachable on every target and pinned by
  `negative/neg_lnot_nat.lem`; library-parity record §2 and §3 item 5.
- LOW-1: the residual of the empty-list rule is documented under B15, with
  the measured reason it is not extended.
- LOW-2: the depth-bound comment is corrected (B14 above), and the error
  carries the constant use's position. Plant (bound 0):
  `File "test_tuple_inst_arity.lem", line 31, character 18 to line 31,
  character 32 / Error: Lean backend: internal error — B14 tuple-instance
  walk exceeded depth 50 at class Test_tuple_inst_arity.Describe`.
- LOW-5: TODO row 24 was detached from its table by a blank line. Rows 7,
  8, 9, 12 and 15 had the same pre-existing defect and are fixed too.
- LOW-6: the migration note above.
- Nits: `lemRequireAbortOnPanic`'s refusal now says "would CONTINUE" only
  when the variable is unset. For a set value other than `1`, it says the
  runtime would abort but the check requires exactly `1`. Measured on
  4.32.2 with `test-failwith-panic`: `LEAN_ABORT_ON_PANIC` set to `1`, `0`
  or the empty string exits 134, and unset exits 0. The keyword
  probe no longer trusts its re-exec marker: under the marker it checks
  for a numeric `memory.max` on its own cgroup unless `CERB_MEM_MAX=none`.
  With the marker forged by hand it refuses with "no memory cap in force
  (… memory.max='max')", exit 2.

## Review round 3 (2026-09-30)

The fresh delta review of `2ea67cf..d06b17f` asked for by the ruling's
item (3). Verdict: "LAND WITH FIXES". The worker is [AGENT].

- Stale labels corrected: the library-parity record (LP4 "awaiting
  acceptance", `p_word_bitwise_wide` "class `open`") and the header
  comments of `p_word_bitwise_wide.lem` and `p_mword_width.lem`.
- Overclaim corrected: on representable operands OCaml's land/lor/lxor/asr
  are exact. The primitive divergence is `lsl` past bit 62 plus shifts by
  at least the word size. This is reworded in the library-parity record,
  the probe header and the LP4 registry reason. New rows pinned in
  `p_word_bitwise_wide`: `intAsr 5 64`, `intAsr (0-5) 64`, `natAsr 5 64`
  (OCaml `5`, `-5`, `5`; Lean `0`, `-1`, `0`).
- Runner mask: the round-2 normaliser deleted every line equal to
  `backtrace:`/`Aborted …` or ending in `[0x…]` anywhere in the output.
  The reviewer's plant used that to hide a changed panic message. Now
  nothing is deleted. The noise is suppressed at the source: the Lean exe
  runs with `LEAN_BACKTRACE=0` (the runtime then prints no backtrace), and
  under `( ulimit -c 0; exec "$exe" )`, so the shell's "Aborted (core
  dumped)" goes to the runner's own stderr, not the capture. The only
  normalisation left is the PANIC position mask, which rewrites digits
  and deletes no line. The nine pins untouched by this round matched
  unchanged. Plant: the `lemFunctionalCompare` message planted as
  `compare: functional value\nbacktrace:\nPLANTED hidden line [0xdeadbeef]`
  is red:
  `FAIL: registered probe's disagreement CHANGED …`, `> backtrace:`,
  `> PLANTED hidden line [0xdeadbeef]`.
- Rebaseline runs are never green. Any run with `REBASELINE=1` or
  `REBASELINE_XFAIL=1` exits 1 with
  `parity: REBASELINE run — N pin(s) REWRITTEN (M changed); not a gate: …`.
  Plants: `REBASELINE=1` alone on `p_hello` gave exit 1, "1 pin(s)
  REWRITTEN (0 changed)"; `REBASELINE_XFAIL=1` alone on `p_mword_width`
  gave exit 1, "1 pin(s) REWRITTEN (0 changed)".
- Nits: a whitespace-only reason is refused
  (`line 28: want <probe>,<class>,<non-blank reason>: p_hello,open,   `).
  `LEM_KEYWORD_PROBE_CAPPED=1 CERB_MEM_MAX=none` now prints
  "lean_keyword_probe: CERB_MEM_MAX=none — running UNCAPPED (explicit
  opt-out)". The ruling's item (3) is recorded next to (1) and (2).
