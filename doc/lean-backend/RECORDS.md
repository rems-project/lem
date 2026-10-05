# Index of the Lean backend's dated records

The front documents ([README.md](README.md), [DESIGN.md](DESIGN.md),
[TODO.md](TODO.md), the [manual chapter](../manual/backend_lean.md))
describe the backend as it is. How it got there, the measurements behind
each decision, and the operator's rulings are in the dated records listed
here. The records are historical: each describes the code at its own date,
and later records may supersede it. They stay at their paths, which other
repositories cite.

Records are in `doc/lean-backend/` unless the path says `doc/notes/`.
Grouped by topic; within a group, by date. Records marked *historical*
describe a design that is no longer current.

## Whole-backend reviews

- 2026-08-31 [Backend quality review](2026-08-31_backend-quality-review.md):
  an independent review of the fork's delta against upstream, against four
  aims (small blast radius for non-Lean users, obviously right Lean output,
  clear design, upstreamable). Source of several TODO items (3, 4, 5, 6,
  36–39).

## Effects, failures and axioms

- 2026-04-09 [`doc/notes/` Inhabited design](../notes/2026-04-09_inhabited_design.md)
  (*historical*): the original fallback-inhabitant design, replaced by
  derived instances.
- 2026-04-12 [`doc/notes/` Effectful target reps](../notes/2026-04-12_effectful_target_reps.md)
  (*historical*): why Lean's optimiser breaks pure-typed effectful
  representations; the later `effectful` declare, itself since removed.
- 2026-04-12 [`doc/notes/` Monadic lifting](../notes/2026-04-12_monadic_lean_backend.md)
  (*historical*, not adopted): a proposal to lift generated code into a
  monad.
- 2026-08-20 [`doc/notes/` Derived Inhabited and failure threading](../notes/2026-08-20_arc8-inhabited-threading-design.md):
  the design of derived bounded `Inhabited` instances and `failwithI`
  binder threading, which is current.
- 2026-08-31 [Effect retirement: summary for external review](2026-08-31_effect-retirement-external-review.md):
  the plan to delete the `runEffectful` axiom and replace effectful
  counters by supply lifting, written for consumer review.
- 2026-08-31 [Fix-first record](2026-08-31_L0-fix-first-record.md):
  fixes from the quality review: contextual keywords, the non-Lean
  regression net (`make nonlean-regress`), single evaluation of tuple-let
  right-hand sides, char escapes, `setChoose`; `integerDiv` verified
  correct.
- 2026-08-31 [Features record](2026-08-31_L1-features-record.md): supply
  lifting and `reader_consumer` built; a per-declaration fuel budget
  built, later removed as a magic value.
- 2026-08-31 [Audit log](2026-08-31_arc-audit-log.md): the audit verdicts
  for the fix-first and features records above and for the deletion
  record below.
- 2026-09-01 [Deletion record](2026-09-01_L2-deletion-record.md): the
  `runEffectful` axiom and the `effectful` mechanism deleted; the declare
  now refused.

## Instances, comparisons and names

- 2026-08-22 [`doc/notes/` Instance-priority lattice](../notes/2026-08-22_arc14-instance-priority-lattice.md):
  the normative priority table (its priority-50 fallback row is obsolete;
  see DESIGN.md).
- 2026-08-22 [`doc/notes/` Reserved names](../notes/2026-08-22_arc14-reserved-names.md):
  the contract for names the backend synthesises (`lemFuel`,
  `_lemReader_`, …).
- 2026-09-29 [`doc/notes/` Comparison dictionaries](../notes/2026-09-29_comparison-dictionaries-design.md):
  threading `[Ord a]`/`[BEq a]` binders guided by Lem's instances, and
  loud comparison of function-typed fields; the open-type-variable
  fallback instances deleted.

## Parity with the OCaml target

- 2026-09-03 [Parity-fix record](2026-09-03_parity-fix-record.md): the
  numeric, set/map and ordering fixes that make Lean compute what OCaml
  computes; the `LemUnsupported.` refusal mechanism.
- 2026-09-03 [Exception-case rulings](2026-09-03_exception-case-rulings.md):
  [USER 2026-09-03] zero discrepancies, with three exception classes; the
  ruling that OCaml-execution limits (63-bit `int`) are not mirrored; the
  2026-09-04 addendum ruling that `int32`/`int64` conversions wrap.
- 2026-09-03 [String-representation design](2026-09-03_string-representation-design.md):
  how Lem strings become bytes on Lean; not implemented (TODO item 31).
- 2026-09-30 [Library parity coverage](2026-09-30_library-parity-coverage.md):
  machine-word and bitwise fixes; [USER 2026-09-30] rulings accepting
  the 63-bit bitwise and run-time word-width differences as OCaml-target
  deviations; the input classes still awaiting rulings (TODO item 33).

## Fuel, totality and measures

- 2026-08-18 [`doc/notes/` Totality mechanisms](../notes/2026-08-18_arc3-totality-mechanisms.md)
  (*historical*): the first fuel and reader compositions, built on a
  library default fuel since removed.
- 2026-09-03 [Fuel-parameter design](2026-09-03_fuel-parameter-design.md):
  [USER 2026-09-03] fuel is a quantified parameter, never a numeral; the
  design of the ambient `[LemFuel]` binder.
- 2026-09-04 [Fuel-parameter record](2026-09-04_fuel-parameter-record.md):
  the fuel lifting built; every LemLib bounded recursion classified; open
  decisions D1 (`Pset.tc`, TODO item 41) and monotonicity (TODO item 13).
  [Pre-merge audit](2026-09-04_fuel-parameter-audit-premerge.md).
- 2026-09-04 [Structural-declare record](2026-09-04_structural-declare-record.md):
  `declare {lean} structural`; the `int32` wrap implemented; the
  monotonicity exemplar.
- 2026-09-04 [Fuel-measure record](2026-09-04_fuel-measure-record.md):
  `fuel_measure` and its sufficiency obligation; the ruling [USER
  2026-09-04] "we don't change the lem structure for ocaml".
  [Pre-merge audit of both](2026-09-04_structural-measure-audit-premerge.md).
- 2026-09-04 [Derived-size record](2026-09-04_d2-enablers-record.md):
  backend-derived `t.lemSize`; fuel'd equalities usable as instance
  methods; fuel-lifted inductive relations.
  [Pre-merge audit](2026-09-04_d2-enablers-audit-premerge.md).
- 2026-09-05 [Measure-hypothesis record](2026-09-05_measure-hypothesis-record.md):
  `fuel_measure … assuming H`. [Pre-merge audit](2026-09-05_measure-hypothesis-audit-premerge.md)
  (finding F1: a contradictory hypothesis proves its obligation
  vacuously).
- 2026-09-05 [Point-free tails and `Pmap` laws](2026-09-05_tails-and-pmap-laws-record.md):
  hoisting trailing lambdas into the head for measured and structural
  definitions; `lean-lib/LemLibPmapLaws.lean`.
  [Pre-merge audit](2026-09-05_tails-pmap-audit-premerge.md).

## Readers

- 2026-09-19 [N-ary `reader_seed`](2026-09-19_nary-reader-seed-record.md):
  one seed per declared reader, in global sorted reader order.
- 2026-09-20 [Fuel with readers in mutual blocks](2026-09-20_fuel-mutual-reader-record.md):
  the refusal of fuel plus reader lifting in a mutual block removed.
- 2026-10-05 [Instance-implicit readers](2026-10-05_instance-reader-record.md):
  `reader val r = instance `Cls.field`` and `reader_consumer val f =
  instance r` — the reader lifting with a type-class binder (the
  `[LemFuel]` shape), built for Cerberus's switch set (PNVI arc S0); the
  byte-identity witness for code that does not use it.

## Documentation and public release

- 2026-09-02 [Docs release-hygiene record](2026-09-02_docs-release-hygiene-record.md):
  the front documents rewritten to describe the system as it is; this
  TODO register created.
- 2026-09-24 [Public-readiness review](2026-09-24_public-readiness-review.md)
  of lem-lean and Cerberus Lean, with its required (MUST) and
  recommended (SHOULD) items.
- 2026-09-24 [MUST remediation](2026-09-24_public-readiness-remediation.md),
  its [delta review](2026-09-24_public-readiness-must-delta-review.md)
  and [closure](2026-09-24_public-readiness-closure.md): bare `sorry`
  representations refused, the repository-local `scripts/capped`, the
  published build path.
- 2026-09-25 [Follow-up](2026-09-25_public-readiness-followup.md) and its
  [delta review](2026-09-25_public-readiness-should-delta-review.md): the
  SHOULD items, licence notices, hash-bearing `lem -v`.
- 2026-09-25 [Branch and worktree inventory](2026-09-25_branch-worktree-inventory.md):
  a snapshot of branches and worktrees, with advisory classification.

## Second consumer: linksem

- 2026-09-28 [linksem findings](2026-09-28_linksem-findings.md): defects
  found by generating linksem (B1–B15, fixed); the audit follow-up (A1–A5:
  comparison fixes, `lemRequireAbortOnPanic`, the open discrepancies A1-R
  and A5); the native-seam rulings ([USER 2026-09-30] `lemSeqImpl`
  temporary, `lemFailStop` removed); the move to Lean 4.32.2; the
  `lemFailStop` migration note.

## Output readability

- 2026-10-03 [Output-niceness record](2026-10-03_output-niceness-arc-plan.md):
  a Lem developer's feedback on the output; comments carried over, the
  `lem:` marker, the layout pass, mutual records as structures, the
  printer cleanup; package A (layout engine, §11; TODO item 42, closed); packages C and D deferred (TODO items 27, 28); the
  upstream report tray scope.

## Correctness and fail-closed hardening

- 2026-10-03 [Backend-hardening record](2026-10-03_backend-hardening-record.md):
  package A of the arc that acted on the read-the-code review and the
  behavioural noodler of 2026-10-03 — the Lean annotation words as
  `target_rep` parameters, keyword and generated-name record fields, type
  variables renamed on collision, the mutual-record update base bound
  once, the layout printer's exponential re-decision, the 128-field
  run-time limit refused, the `termination_argument` promise corrected,
  fail-open spots and state fixes; the `min`/`max` OCaml-target deviation
  registered ([USER 2026-10-03] "Register as deviation", rulings X5).
  Its "Package C" section (same day) is the cleanup slice: dead code and
  LemLib's dead definitions deleted with per-name consumer-grep evidence,
  one reserved-name table, one instance-priority constant, the comment and
  message sweep, the TODO 39 test, and the gate tails per commit. Its
  "BEq-lattice slice" section (same day) lands the ruling on the
  [BEq instance-lattice design note](2026-10-03_beq-instance-lattice-design.md)
  ([USER 2026-10-03] "(a) 450/400"): the `[Eq0 a] : BEq a` bridge at 450
  and the comparator bridges at 400, below core's `BEq`; the kernel
  agreement theorems (`LemLibTheorems`, namespace `BeqLattice`), the
  plant-tested probe legs, the before/after census of both consumers, the
  Cerberus re-pin patch
  ([`2026-10-03_beq-lattice-cerberus-repin.patch`](2026-10-03_beq-lattice-cerberus-repin.patch)),
  the cerberus-sl re-pin note and the TODO 45 re-measurement.
- 2026-10-03 [BEq instance-lattice design note](2026-10-03_beq-instance-lattice-design.md):
  the design pass ruled "Design pass first" on code-review finding L1 —
  the lattice as measured (core's `BEq` at 500, the undocumented tie),
  the consumer census, options (a)–(d) and the recommendation the
  operator adopted.

## When the front documents were checked

- 2026-09-25: the public-readiness work checked README.md end to end
  against `fd048db` ([follow-up evidence](2026-09-25_public-readiness-followup.md));
  the manual chapter's banner records the same check. The quickstart
  measurement then used OCaml 5.4.0, opam 2.1.5 and Lean 4.28.0.
- 2026-10-03: README.md, DESIGN.md, TODO.md and this index were
  reconciled by reading against the source at `2e54ff0`; no build was run
  for that.
- 2026-10-03, later: after the arc's pre-merge audit, DESIGN.md's layout
  claims, the three banners and TODO.md's line references were corrected
  against the audit-fix commit `131b922`. The last recorded test-suite run
  is the one quoted in the
  [output-niceness record](2026-10-03_output-niceness-arc-plan.md) §13.
- 2026-10-03, backend hardening (package A): DESIGN.md (records and
  fields, the field-count limit, type-variable renaming, the
  `termination_argument` row, the deviation register, the layout printer's
  sharing), the manual chapter's three matching claims and TODO.md were
  updated for the changes in the
  [backend-hardening record](2026-10-03_backend-hardening-record.md), whose
  gate run is quoted there; README.md was not touched (its claims were
  checked against the change list and none moved).
- 2026-10-03, BEq-lattice slice: DESIGN.md ("Instance priorities come
  from one table", the `termination_argument … = automatic` row), TODO.md
  (46 closed, 45 re-measured, the `src/lean_backend.ml` line references
  re-derived by grep after the slice's edits), the lattice note's
  2026-10-03 addendum and this index; the gate run is quoted in the
  [backend-hardening record](2026-10-03_backend-hardening-record.md),
  "BEq-lattice slice"; the manual chapter's two matching paragraphs
  (the `termination_argument … = automatic` limit and the priority table)
  were updated with them. README.md was checked against the change list;
  none of its claims moved.

## Elsewhere

- Upstream Lem report drafts: [`doc/upstream-tray/`](../upstream-tray/)
  (TODO item 30).
- The noodle record (`2026-09-03_noodle-backend.md`) cited by the
  parity-fix record is on branch `noodle/backend`, not in this tree.
