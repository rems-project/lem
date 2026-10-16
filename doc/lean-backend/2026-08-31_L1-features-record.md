# L1 feature-slice record — 2026-08-31

Provenance: L1 worker slice of the effect-retirement arc (charter:
cerberus-lean `lean_frontend/docs/2026-08-31_effect-retirement-design.md`
@ 913ee31d1, §8.1 L1; S0 record read — its S0-F1 finding concerns C1's
migration design, not these backend features' semantics; L0 base
4fd4d50). Branch `arc/effect-retirement`. All decisions [AGENT] unless
marked; quoted outputs are verbatim; tallies marked "derived" are
derived. `runEffectful` and the `effectful` class are deliberately
UNTOUCHED (they die in L2); the LemLib axiom cluster is untouched.

## Commits

| Feature | Commit | Charter | Disposition |
|---|---|---|---|
| 1. Supply lifting (`declare {lean} supply val`) | 383b996 | §3.2 | BUILT, full battery green |
| 2. `reader_consumer` (`declare {lean} reader_consumer val`) | 195b683 | §4.2 | BUILT, full battery green |
| 3. Per-declaration fuel budgets (`declare {lean} fuel val f = N`) | 40df3a8 | §8.3 | BUILT, opt-in constraint held structurally |
| — | (this record's commit) | — | record + late G-infix probe |

## Feature 1 — supply lifting: spec conformance (charter §3.2)

Mechanism as specified: state-passing (supply-threading) transform on
the reader-lifting pipeline — declare (contextual-keyword grammar row,
L0 mechanism, no new hard keyword) → typecheck `supply : Targetset.t`
on `const_descr` → `lean_supply_prepass` fixpoint over the call graph
at Val_def granularity (persisting across modules; instances skipped;
threading ARITY recorded per liftable cref) → threaded emission.

- **Annotation surface**: `declare {lean} supply val f`,
  target-scoped; G-type enforces `f : unit -> nat` (also accepts the
  synonym-mapped `natural`; noted below). No `supply_seed` built (v1,
  per spec: fail-closed minimalism).
- **Signature transform**: binder order [Inhabited] → readers →
  `(_lemSupply_<name> : Nat)` per supply (sorted-name order) →
  original params; result type becomes `((τ) × Nat …)` — one `× Nat`
  per supply, same order. Verified by TestSupplyCheck signature pins.
- **Body transform**: `supply_thread`/`supply_block` A-normalize
  draws, threaded calls, and control forms in LEFT-TO-RIGHT
  DEPTH-FIRST order (charter O1); a draw is
  `let (v, s') := LemLib.supplySplit s` (`supplySplit s = (s, s+1)` —
  the ONE LemLib addition: a plain def, kernel-transparent, no
  axiom/IO; the axiom cluster untouched). If/match arms return the
  value×states pair; only the taken branch consumes (pinned).
- **O7 determinism is structural**: the transform emits let-bindings,
  tuples, `supplySplit`, and the source's own control forms; no
  nondeterminism constructor exists anywhere in its emission (stated
  in the code header, DESIGN.md, and checkable by reading
  `supply_thread` — there is no ND builder to grep). [derived check
  CORRECTED by the audit (minor-5): the originally quoted
  `grep -c 'ND\.' = 0` does not reproduce — the pattern has one FALSE
  POSITIVE, a comment substring ("LEAN_BACKEND.ML" at :191). The
  check as actually needed, re-run and quoted verbatim in the
  audit-response addendum below:
  `grep -nE '\bND\.[a-z]|msum' src/lean_backend.ml` → no matches
  (exit 1).]
- **Seeding**: entry points pass the initial value explicitly and
  receive the final value in the returned pair (no baked seed — the
  shape (b) the charter's entry decision consumes).
- **St discipline**: all new state in `St` with lifetime classes —
  `supply_lifted`/`supply_arity`/`supply_params_cache` [invocation],
  `supply_binder`/`supply_name_counter`/`supply_head_ok` [render] —
  wired into `St.reset_invocation`. NO new process-global refs; the
  `on_cr_simple_applied` class was not added to.
- **Compositions** (all spec'd, all tested): reader (binder order
  defined + pinned), reader_seed (seed defs ARE supply-liftable — the
  mini_pipeline shape; seed-name reader injection + supply binder
  coexist), fuel (worker threads the supply through the decremented
  self-call; the zero-fuel arm returns the sentinel with the supply
  UNCONSUMED; wrapper type gains supply arrows), multi-supply
  (independent streams, sorted order), and the tuple-let path rides
  the L0 single-RHS emitter (below).
- **Effectful mix**: `supply`×`effectful` on one val is a
  generation-time error (transitional rule; probe).

**Guard inventory → negative probes** (each probe asserts its declared
error fragment; suite `lean-negative`):

| Guard | Error fires at | Probe |
|---|---|---|
| G-λ (draw/lifted use under lambda) | transform | `neg_supply_lambda.lem` |
| G-bare (bare lifted/supply reference; incl. HOF) | transform + net | `neg_supply_bare.lem` |
| G-inst (instance method) | Fun_def/Let_def guard | `neg_supply_instance.lem` |
| G-rel + net (indreln/lemma/assert/non-threaded reach) | exp net (App/bare/Infix legs) | `neg_supply_indreln.lem` |
| G-arity (supply const arity; exact threading arity at calls) | transform | `neg_supply_arity.lem` |
| G-infix (lifted/supply constant infix) | transform + net | `neg_supply_infix.lem` |
| G-type (supply val not `unit -> nat`) | param sweep | `neg_supply_type.lem` |
| mix (supply × effectful/reader/reader_seed) | param sweep | `neg_supply_mix.lem` |
| truly-mutual block (v1 restriction, extend-on-need) | Fun_def guard | `neg_supply_mutual.lem` |
| reserved `_lemSupply` binder prefix | reserved-name contract | `neg_supply_shadow.lem` |

Multi-clause note: the >1-clause group guard exists as a fail-closed
backstop but is UNREACHABLE from lem source — the pattern compiler
folds multi-clause defs into one match before the backend, and the
compiled match THREADS CORRECTLY; converted to a positive case
(`clausy` in test_supply.lem, pinned). Not a deviation: the charter
never required rejecting multi-clause sources.

**Tuple-let single-evaluation (brief item e).** Expression-level
destructuring over a drawing RHS threads through ONE binding
(`destructure_once`, pinned: third draw is s+2 — a duplicated RHS
would give s+4). Top-level multi-name destructuring rides L0's
single-RHS emitter: one `private def lemLetRhs_*` (threaded) + one
threaded call per projection — within a call the RHS draws exactly
once (`top_a 500 = (500, 502)`: two draws, not four). Semantics note
(deliberate, documented): a supply-lifted top-level VALUE binding
becomes a function of the supply, so each projection call re-runs the
RHS with its caller's supply — the state-passing semantics of a
drawing value binding, deterministic and pinned; the effectful
mechanism's once-at-init semantics is not claimed for it.

## Feature 2 — reader_consumer: spec conformance (charter §4.2)

As specified: `reader_consumer : Targetset.t` on `const_descr`;
consumer uses count as reader uses in the lifting fixpoint (callers
lift); call sites pass ALL reader parameters as extra leading
arguments in the global sorted order, injected exactly once via the
bare-Constant repair `(rep _lemReader_…)`; bare/HOF references repair
by type-preserving partial application; **injection routes through
`reader_inject_name`**, so inside a `reader_seed` def the SEED's first
argument is picked up with no new machinery — probe-verified emission:

    def  seedy  (cfgv : Nat) (x : Nat)  : Nat := ( RCImpl.scaled cfgv)  x

**Guard inventory → probes**: RC-rep three legs (missing rep
`neg_rc_norep.lem`; parameter-binding rep `neg_rc_paramrep.lem`;
non-simple forms — same sweep, message "unsupported Lean target_rep
form"); RC-mix `neg_rc_mix.lem` (× reader/reader_seed/supply/
effectful, one sweep); RC-inst `neg_rc_instance.lem` (via the
extended `exp_needs_reader` + the existing instance guard); RC-rel/
scope `neg_rc_indreln.lem` (any consumer call without a reader value
in scope — indreln, lemmas/asserts, non-lifted contexts). Plus an
infix-position rejection in ordinary emission and a consumer-head
case in the supply transform (consumer calls with supply-drawing
arguments inject readers correctly).

Finding (positive, recorded): an infix USE of an operator-named
consumer arrives at the backend as an App node (lem decomposes rep'd
operator applications), and injects CORRECTLY —
`(RCImpl.op _lemReader_cfg) a 2` (probe-verified); the Infix-node
guard is a backstop with no lem-source reproducer found.

Tests: `test_reader_consumer.lem` (plain/lifted/seed/bare-HOF
contexts; the seed-rooted entry is .lem-assertable and asserted),
`TestReaderConsumerCheck.lean` (rfl pins), compiled
`TestReaderConsumerExec.lean` (phase `lean-reader-consumer`),
`invariance/inv_reader_consumer.lem`.

## Feature 3 — fuel budgets: spec conformance (charter §8.3 + brief)

Syntax `declare {lean} fuel val f = <N>` (numeric Num row beside the
backtick sentinel row; LR conflict counts unchanged). Attachment
exactly per the review's map: one `Targetmap` field (`fuel_budget`)
beside `fuel_sentinel` → typecheck `Decl_fuel_budget` case →
`fuel_budget_for` consulted at ONE place, the wrapper emission,
replacing the literal ` lemDefaultFuel` only when a budget is
declared. Workers, threading, self-call discipline untouched.

**THE HARD CONSTRAINT (consumer-ratified, §8.3) HOLDS STRUCTURALLY:**
unannotated declarations emit the identical ` lemDefaultFuel` text —
the only code path difference is `match fuel_budget_for c with None ->
" lemDefaultFuel"`. Witnessed three ways: (i) the pre-existing corpus
tree-diff (below) is byte-identical; (ii) probe: an unannotated
sibling in the same file emits `dspin_lemFuel lemDefaultFuel`
verbatim; (iii) the compiled boundary test (below) shows the
unannotated sibling cutting at exactly 10^6. No stop-and-report was
needed.

Guards → probes: budget without sentinel (`neg_fuel_budget_nosentinel.lem`),
non-positive budget (`neg_fuel_budget_zero.lem`); both swept for every
budget-marked constant even if unused. The human-target echo emits
the plain literal (round-trips; the m1 echo discipline). L0's
`lemDefaultFuel` reserved-def-name guard already protects the default
reference. Compositions: reader (`climb`, budget 7, wrapper keeps the
reader-prefixed type) and supply (`fuel_draws_b` in test_supply.lem,
budget 3 — exhaustion mid-stream returns the partial draw list with
the supply at the cut, pinned).

## Compiled-test evidence (verbatim, at 40df3a8 + the record commit's probe)

`tests/comprehensive/lean-test/.lake/build/bin/test-supply-draws`:

      ok: draw_two 100 () = ((100, 101), 102)
      ok: destructure_once 30 () = ((30, 31, 32), 33) [RHS draws once]
      ok: top_a 500 = (500, 502) / top_b 500 = (501, 502) [projections: one RHS call each]
      ok: uses_both 9 40 3 = (52, 41) [reader x supply]
      ok: uses_seeded 40 3 = (85, 41) [reader_seed x supply]
      ok: fuel_draws 60 2 = ([60, 61], 62) [fuel x supply]
      ok: fuel_draws_lemFuel 1 60 2 = ([60], 61) [exhaustion leaves supply at cut]
      ok: two_streams 10 100 () = ((10, 100, 11), 12, 101) [independent streams]
    supply draws: OK
    exit=0

`test-reader-consumer`:

      ok: uses_scaled 9 3 = 903 [lifted caller injects]
      ok: uses_scaled_and_cfg 9 3 = 912 [consumer + direct read]
      ok: maps_scaled 9 [1,2] = [901,902] [HOF partial application]
      ok: via_seed 3 = 1407 [reader_seed pickup through consumer + lifted callee]
    reader_consumer: OK
    exit=0

`test-fuel-budget`:

      ok: bspin 4 = 0 [within budget 5]
      ok: bspin 5 = 999 [exhausts at budget 5]
      ok: dspin 999999 = 0 [unannotated runs to lemDefaultFuel]
      ok: dspin 1000000 = 999 [unannotated cuts exactly at lemDefaultFuel]
      ok: climb 10 4 = 10 [reader x budget: completes under 7]
      ok: climb 20 4 = 998 [reader x budget: exhausts at 7]
    fuel budget: OK
    exit=0

The elaborator/kernel pins (TestSupplyCheck.lean — `rfl` proofs of the
exact draw sequences, the charter-O1 order evidence — and
TestReaderConsumerCheck.lean) all elaborate in the suite build.

## Invariants at close (verbatim)

- Non-Lean regression net, at the final tree:

      nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)

  Re-run green after EACH feature commit; zero drift at every check —
  no stop-and-report event occurred.
- Pre-existing comprehensive corpus, generated by the L0-base lem
  (scratch build of 4fd4d50 via `git archive`) vs this slice's lem,
  sha-compared per file: first check (post-F1, 43 pre-existing tests
  = 86 .lean files) printed verbatim `TREE-BYTE-IDENTICAL`; the
  post-F2/post-F3 re-checks (84 files — `test_contextual_keywords`
  excluded after its SOURCE was deliberately extended with the two
  new words) reported zero `DIFF:` rows. No pre-existing generated
  file changed; the only corpus deltas are the new test files and the
  contextual-keyword test's own new rows.
- Full battery at the final tree:

      === Generation: 47 passed, 0 failed, 0 skipped ===
      Build completed successfully (134 jobs).
      FULL SUITE EXIT: 0

  incl. both panic-pin legs, the m7 and M2 pins, the three new
  compiled phases, and 32/32 negative probes (15 pre-slice + 10
  supply + 5 reader_consumer + 2 fuel-budget; every row
  `OK (rejected as declared)`). [Breakdown arithmetic CORRECTED by
  the audit (minor-4): the original text said "11 supply", which
  sums to 33 — the true supply count at this record's commit is 10
  (incl. the late G-infix probe) and the stated total 32 was right.]
- New `lean-invariance` phase (charter §6.3's non-Lean invariance
  test, built this slice): each `invariance/inv_*.lem` generated for
  ocaml/hol/isa/coq with and without its `declare {lean}` lines,
  byte-compared; verbatim:

      OK: inv_fuel_budget.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
      OK: inv_reader_consumer.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
      OK: inv_supply.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)

  Plant-tested both directions: a declare-free file →
  `FAIL (vacuous): inv_plant.lem contains no 'declare {lean}' lines`
  (exit 1); stripping a semantic line instead → FAIL with the diff
  rows (`Only in invariance/_out/decl: inv_supply.ml` …, exit 1);
  both plants reverted. (The echoing/human targets re-render declare
  lines by design and are covered by the L0 golden net instead —
  matching the L0 record's live-catch finding.)
- lean-lib: `Build completed successfully (35 jobs).` (capped). The
  ONLY LemLib delta this slice is `LemLib.supplySplit` (one plain
  def; justification: the charter names it as the draw primitive —
  greppable, kernel-transparent). The runEffectful axiom cluster is
  byte-untouched (dies in L2, not here).
- ocamlyacc at the final grammar, verbatim: `5 rules never reduced` /
  `2 shift/reduce conflicts, 2 reduce/reduce conflicts.` — identical
  to the L0 record's counts; both new words ride the contextual-
  keyword mechanism and are asserted usable as ordinary identifiers
  by the standing `test_contextual_keywords.lem` (rows added, sum
  re-pinned).

## Deviations / notes, flagged loudly

1. **Manual not rewritten.** Charter §6.3 lists "lem manual entry
   beside the reader declare"; the reader has NO manual entry — the
   manual (`doc/manual/backend_lean.md`) is the review's m5
   registered-stale item (its rewrite is a priced item of its own).
   All three features are documented where reader/fuel actually live:
   `doc/lean-backend/DESIGN.md` (new sections + declare-table rows).
   [AGENT] call; flag for the operator if the manual entry is wanted
   in-arc.
2. **Charter §6.3's "run before (against the effectful scaffold) and
   after … the swap"** describes the C1-side equivalence at the
   `symbol.lem` declare swap; it is not executable in L1 (no model
   swap here). L1's compiled tests pin the threaded semantics
   absolutely (exact sequences), and L0's m7 pin covers the effectful
   scaffold side; the before/after differential at the swap is C1's
   battery.
3. **G-type accepts `natural` as well as `nat`** (both map to Lean
   `Nat`); the charter says `unit -> nat`. Superset, documented in
   the guard message's spirit; flag for the reviewer.
4. **Supply-lifted top-level value bindings** have state-passing
   (per-use) semantics, not the effectful once-at-init semantics —
   deliberate, documented in DESIGN.md and in Feature 1 above, and
   irrelevant to the cerberus clients (all function defs).
5. **Defs carrying a Lean target_rep are excluded from supply
   lifting** (their bodies are dead text; their call sites emit the
   rep, which cannot take a supply). Deliberate divergence from the
   reader pre-pass (which lifts them), documented at
   `lean_supply_prepass`; the alternative silently injects state into
   a hand-written rep.
6. Scratch hygiene: `.l1-scratch/` (probes + the 4fd4d50 comparison
   build) is ephemeral and deleted at slice end; every load-bearing
   probe output is quoted verbatim here or committed as a test.

## Audit-response addendum (2026-08-31, post-a51615e)

The L1 fresh audit returned MERGE-SAFE-WITH-NOTES with one MAJOR;
ruling [AGENT, orchestrator-relayed]: fix properly (defect against
charter O1), one audit-response pass. All items below land in this
addendum's commit.

**MAJOR-1 — short-circuit operands were threaded strictly: FIXED.**
`supply_thread`'s Infix path hoisted right-operand draws above `&&`/
`||`, consuming supply on the short-circuit path where the
pre-transform Lean (macro_inline and/or) and the OCaml oracle draw
nothing — an O1 violation. Fix: a `lean_shortcircuit_kind` classifier
(head constants whose Lean rep is `CR_infix` `&&`/`||`) routes a
drawing RIGHT operand to `supply_shortcircuit`, which emits the
branch structure (`a && b ≡ if a then b else false`;
`a || b ≡ if a then true else b`) with the right operand as a supply
arm — draws fire only when the operand evaluates; the LEFT operand
stays strict (both references evaluate it); a pure right operand
keeps the old (correct) path byte-for-byte. The application-spine
leg gets the same treatment when fully applied and a fail-closed
error for partial/over-application. `-->` (lem `imp`, inlined to
`(not x) || y`) rides the same path — verified.

Kernel-pinned results (TestSupplyCheck.lean, all `rfl`; the auditor's
shapes and duals, verbatim from the test file):

    example : sc_and 10 false = (false, 10) := rfl   -- short-circuit: no draw
    example : sc_and 7 true = (true, 8) := rfl       -- right draws 7 (= 7)
    example : sc_and 10 true = (false, 11) := rfl    -- right draws 10 (≠ 7)
    example : sc_or 10 true = (true, 10) := rfl      -- short-circuit: no draw
    example : sc_or 7 false = (true, 8) := rfl       -- right draws 7 (= 7)
    example : sc_or 10 false = (false, 11) := rfl    -- right draws 10 (≠ 7)
    example : sc_both 1 () = (false, 3) := rfl       -- left draws 1 (=1), right draws 2
    example : sc_both 5 () = (false, 6) := rfl       -- left draws 5 (≠1): ONE draw only
    example : sc_nested 10 true false = (true, 10) := rfl   -- outer || short-circuits
    example : sc_nested 10 false false = (false, 10) := rfl -- inner && short-circuits
    example : sc_nested 10 false true = (false, 11) := rfl  -- inner right draws 10
    example : sc_nested 5 false true = (true, 6) := rfl     -- inner right draws 5 (= 5)
    example : sc_imp 10 false = (true, 10) := rfl    -- vacuous antecedent: no draw
    example : sc_imp 7 true = (true, 8) := rfl       -- consequent draws 7 (= 7)
    example : sc_imp 10 true = (false, 11) := rfl    -- consequent draws 10 (≠ 7)

Compiled witnesses added to the draw-sequence binary (verbatim):

      ok: sc_and 10 false = (false, 10) / sc_or 10 true = (true, 10) [short-circuit: no draw]
      ok: sc_and 10 true = (false, 11) / sc_or 10 false = (false, 11) [evaluating branch draws]
      ok: sc_both 5 () = (false, 6) [left strict, right short-circuited]
      ok: sc_nested 10 false true = (false, 11) / sc_nested 10 false false = (false, 10) [nested]
    supply draws: OK

**minor-1 FIXED**: `lean_param_dup_check` on BOTH sorted param lists —
two reader (or supply) constants sharing an unqualified name is now a
generation-time error naming both full paths. Probes
`neg_supply_dupname.lem` / `neg_reader_dupname.lem` (two-module
reproducers).

**minor-2 FIXED**: a supply val DEFINED by a live lem definition with
no Lean target_rep (ordinary referenceable def + supplySplit'd call
sites = one constant, two semantics) is rejected in the supply
pre-pass; with a Lean rep the body renders as dead comment text and
stays legal (the invariance witness's shape). Probe
`neg_supply_defbody.lem`.

**minor-3 FIXED**: `lean_fuel_budget_check` gains the rep leg (budget
on a target_rep'd val — no wrapper is ever emitted, incl.
reader_consumer implementations), and a new invocation-wide
completeness leg (`lean_fuel_budget_completeness_check`, run once
from `lean_analysis_prepass_all`, which sees every module before any
emission) rejects budgets on constants no Fun_def defines. Probes
`neg_fuel_budget_rep.lem` (auditor shape p8) /
`neg_fuel_budget_speconly.lem` (p3).

**minor-4 FIXED** in place above (probe-breakdown arithmetic: 10
supply probes at a51615e, not 11; total 32 was correct).

**minor-5 FIXED** in place above; the check as actually needed,
re-run at this tree, verbatim:

    $ grep -nE '\bND\.[a-z]|msum' src/lean_backend.ml
    $ echo $?
    1

(no matches; the original pattern's single hit was the comment
substring "LEAN_BACKEND.ML" at :191 — a false positive, corrected.)

**notes (a) — unprobed guard legs, probes added**:
`neg_supply_mix_reader.lem` / `neg_supply_mix_seed.lem` (the supply
mix guard's reader / reader_seed legs), `neg_rc_mix_supply.lem`
(RC-mix supply leg), `neg_rc_infixrep.lem` (RC-rep's
unsupported-form leg — an infix rep).

**C1-brief obligation (audit deviation-4 outcome), recorded for the
orchestrator**: the C1 brief must carry a named item — an explicit
cone check that NO supply-lifted Let_def-bound top-level VALUE sits
in the adopted lifted cone (a drawing value binding has per-use
state-passing semantics under the transform, vs the effectful
mechanism's once-at-init; the census expects only function defs, and
the check makes that expectation load-bearing).

### Invariants re-verified at this addendum's tree (verbatim)

    FULL SUITE EXIT: 0
    === Generation: 47 passed, 0 failed, 0 skipped ===
    Build completed successfully (134 jobs).

41/41 negative probes (`OK (rejected as declared)` × 41: 15 pre-slice
+ 14 supply + 1 reader + 7 reader_consumer + 4 fuel-budget — derived
breakdown); all compiled pins green (supply-draws now 12 checks);

    nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)

Pre-existing corpus emission diff vs a51615e: the FULL a51615e test
corpus (47 sources = 94 generated files, including the supply tests
at their a51615e state) regenerated with the a51615e-scratch lem and
this tree's lem — `diff -r` exit 0, zero rows. NO file's emission
changes from the short-circuit fix: the base corpus contains no draw
under a short-circuit operand (the fix's only trigger); the sc_*
shapes enter the corpus as NEW source in this same commit.
lean-lib: `Build completed successfully (35 jobs).` (untouched this
pass). ocamlyacc, verbatim: `5 rules never reduced` /
`2 shift/reduce conflicts, 2 reduce/reduce conflicts.` (grammar
untouched this pass).
