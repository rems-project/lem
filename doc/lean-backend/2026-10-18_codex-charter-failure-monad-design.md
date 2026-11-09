# Codex charter — the failure-monad translation (TODO item 24): the design pass (2026-10-18, rev 2 after review)

**Branch:** `design/failure-monad` · **worktree:** `worktrees/lem-lean-design/failure-monad` (created by the orchestrator at dispatch
with `scripts/new-worktree.sh lem-lean design/failure-monad`; base = `mdd/lean-backend` at dispatch). **Worker:** one Codex worker.
**This is a DESIGN PASS:** the deliverable is a design note plus a bounded measurement spike; the implementation is chartered
separately after the operator accepts the design. No change to `src/` or `lean-lib/` is landed by this charter.

## 0. Goal and success condition

**Goal.** Decide how lem-lean's Lean backend emits failure as an effect — every function that can transitively reach `failwith`
(and the other failure primitives) returned in an error monad — so that strictness and evaluation order become part of the
semantics rather than a property of Lean's compiler. That translation is the named mover of the temporary native seam `lemSeqImpl`
(`lean-lib/LemLib.lean:276-282`: logically its second argument, at run time forcing the first through an IO reference, so a
`failwithI` inside a sequenced-away expression panics at run time while every kernel theorem about the model sees nothing), of the
open finding A5 (a `let` floated into an untaken branch or a closure — reached on a real corpus: linksem-lean's handoff note of
2026-10-03 attributes all 13 mismatches and 44 different-failure-point cases of a 24,255-case differential to it), of most of A3,
and of A4's evaluation order. The consumer cerberus-caesium carries the seam as a stated boundary on every claim and asked for the
mover (its agent's list, item 3); [USER 2026-10-17] agreed to charter the design pass. TODO item 24 names what the pass must settle.

**Success condition:** a design note `doc/lean-backend/2026-10-18_failure-monad-design.md` that (1) states the translation
precisely — the effect analysis (which functions, how inferred, how declared at `target_rep` boundaries), the monad (`Except`, or
the existing `Exception`/ND shapes where a function already lives in one, and why), the emitted shape for let-bindings, function
application, pattern matches, mutual blocks, readers, supply and fuel threading, and the OCaml-order argument evaluation (A4);
(2) shows on the comprehensive suite's own probes how `f_let_float_branch`, `f_let_float_closure` and the B15/B15b shapes come out,
and that `lemSeq`/`lemSeqImpl` are then deletable; (3) prices the run-time cost with a MEASURED spike whose method is valid (review finding 15): a prototype of the
emission on one lem module chosen because it exercises the proposed binds on BOTH success and failure paths (say why), run on a
bounded effectful workload large enough that start-up is not the measurement, timed as current-binary versus prototype-binary on
the same runtime inputs with generation and compilation EXCLUDED, repeated enough times to expose noise (state the count); the
suite's parity runner is not that instrument (it builds both targets then reports parity); numbers quoted with the commands; the
minimal source and recipe to rebuild the prototype kept WITH the note (no dependence on an orphan scratch branch); if valid
measurements cannot be obtained within the tripwire, the note ships labelled INCOMPLETE ON COST, not as meeting this item; (4) states what happens to proofs over generated code (the measure
sufficiency obligations, the fuel-parametricity pins, the cerberus-lean consumers' theorems that unfold through `lemSeq` and through
pure functions that become monadic), with a migration order for cerberus-lean and an estimate of its proof churn; (5) lists the
boundary rulings it needs from the operator, each with a recommendation; (6) is short (the finding records are long; the design
should be shorter than the linksem findings' native-seams section plus TODO 24).

Rulings this rests on, paraphrased: [USER 2026-09-30] D1(a): the seam is accepted onto the boundary list as TEMPORARY, its named
mover being this translation (findings record, native seams); [USER 2026-10-03] the output-niceness work goes first — it has landed,
so the sequencing constraint is met; [USER 2026-09-04] the lem structure is not changed for OCaml's sake — the OCaml target's output
must be byte-identical before and after (the translation is Lean-only); [USER 2026-09-03] no magic values; standing: zero Lean-vs-OCaml
behavioural discrepancies is the rule and this is the arc that closes three of the known ones; the operator's words are never quoted
verbatim in files or commit messages; design passes are scoped with the operator before dispatch — this charter is that scope.

## 1. What is known (verify what you touch)

| Fact | Where |
|---|---|
| TODO item 24, the questions it names | `doc/lean-backend/TODO.md` row 24 |
| The findings and the seam's ruling | `doc/lean-backend/2026-09-28_linksem-findings.md`: B15/B15b (`let _ = e1 in e2` and unused lets dropped `e1`), A3, A4, A5, and the section "Native seams: boundary rulings (2026-09-30)" |
| The seam | `lean-lib/LemLib.lean:276-282` (`lemSeqImpl`, `lemSeq`); its emission sites in `src/lean_backend.ml` (grep `lemSeq`); the three `implemented_by` seams in LemLib (`failwithIImpl`, `lemSeqImpl`, `fuelExhaustedWithImpl`) |
| The real-corpus evidence for A5 | `/home/dev/projects/linksem-lean/handoff/lem-lean/2026-10-03-a5-let-floating-reached-in-linksem.md` |
| The probes and the parity runner | `tests/comprehensive/parity/probes/f_let_float_branch.lem`, `f_let_float_closure.lem`, `parity/expected_failures.txt` (class `open`), `parity/run.sh`; the suite: `make -C tests/comprehensive lean` |
| The existing effect machinery to build on, not duplicate | the fuel transform (`declare {lean} fuel`, `fuel_measure`), the supply state-passing transform, the reader and instance-reader lifting (`2026-10-05_instance-reader-record.md`), `declare {lean} structural` — all in `src/lean_backend.ml`; the backend manual `doc/manual/backend_lean.md` |
| The consumers that will feel it | cerberus-lean: 268 `lemSeq` sites in generated code at the 2026-09-30 re-pin, two hand-written proofs (`lean_frontend/Driver_lemMeasureProofs.lean:69`, `Core_run_aux_lemMeasureProofs.lean:97`), the allowlist `scripts/unsafebaseio_allowlist.txt`, the boundary list in `VALIDATION.md` §3; cerberus-sl and cerberus-caesium quote generated shapes |
| The prior ruling against a bare transform | cerberus-lean's `docs/2026-09-05_orchestrator-handoff.md` (the operator was unsure a pure-failure lifting transform could be authorised without a proved correspondence; the route accepted then was a lifted twin behind a kernel-checked per-function correspondence) — the design must say how this translation relates to that |

## 2. Deliverables (ordered)

**D0 — Base.** Build lem in the worktree (root `make`) and run the comprehensive suite once; quote its summary and the parity line as
the baseline the spike is compared against.
**D1 — The analysis and emission design** (success items 1, 2), written against the backend's actual structure (cite `lean_backend.ml`
functions and lines).
**D2 — The spike** (success item 3): the prototype emission, its workload, and the timing method of §0; the prototype's minimal
source and the exact commands travel with the note (an appendix or a sibling file under `doc/lean-backend/`), the ephemeral outputs
are deleted; it is evidence, not a landing, and the note says so. Note on the A5 probes: `parity/expected_failures.txt` registers
`f_let_float_branch`/`f_let_float_closure` as expected failures, so a prototype that repairs them makes the runner report an
expected failure now PASSING (`run.sh:42-47`) — that is the intended finding, not a reason to keep the defect or to move any
production baseline in this pass.
**D3 — Consumers and proofs** (success item 4), with the cerberus-lean numbers re-counted on its current mainline (grep, not the
2026-09-30 figures).
**D4 — The note** (success items 5, 6) committed on `design/failure-monad`; one commit, message stating what was measured.

## 3. Flex — what you decide, and when to stop instead

- Yours: the monad choice and emission shapes (recommend; the operator rules), the spike's module, the note's structure.
- Not yours: landing any `src/` or `lean-lib/` change; touching the pins; editing cerberus-lean (read it; count; do not change it).
- **Stop and report when:** the spike cannot compile within the tripwire (record what blocked it; the note still ships with that
  stated); the analysis shows the translation conflicts with the fuel or reader transforms in a way that needs an operator ruling
  before the design can be finished (write the ruling request into §5 of the note and stop there); you are done.

## 4. Rules (binding)

- **Environment.** `source /home/dev/projects/cerberus-lean-proj/scripts/env.sh` (or `scripts/ce`); every Lean build through
  `scripts/capped` (repository-local; `CERB_MEM_MAX` default 64G here, the comprehensive suite's own default 16G); one heavy job at a
  time. Exit 137 or a KILLED banner is a failure.
- **No trust gaps in anything proposed:** the design must not introduce new `unsafe`, `implemented_by`, `extern` or axioms; its whole
  point is to delete one.
- **Provenance and record integrity.** Measured numbers quoted verbatim with the command; derived tallies labelled; your judgements
  [AGENT]; operator rulings only as paraphrased in §0; never a verbatim quotation of the operator. Commit message ends with the
  attribution your harness prescribes.

## 5. Reading list

`doc/lean-backend/TODO.md` (24, and 13 on fuel monotonicity) · `2026-09-28_linksem-findings.md` (whole) · `DESIGN.md` · `doc/manual/backend_lean.md`
· `src/lean_backend.ml` (the transforms) · `lean-lib/LemLib.lean` (the seams and their comments) · `tests/comprehensive/parity/` ·
the linksem handoff note · cerberus-lean `lean_frontend/VALIDATION.md` §3 (boundary list) and `docs/2026-09-05_typed-failure-outcomes-design.md`
(the consumer-side view of pure failures) · `/home/dev/projects/cerberus-caesium/.tmp/filings/2026-10-17_cerberus-lean-note-2.md` and its
agent's list, item 3.
