# Effect retirement: design summary for external review

Audience: the refined-cerberus project (a Lean/iris-lean verifier being
built over the cerberus-lean Core semantics), asked to review this design
as the consumer whose trust story it serves. [USER 2026-08-31]
commissioned this note (a note on the proposed design, in the lem repo,
for the other agent working on refined-cerberus to review).

This is a summary. The governing documents are:

- cerberus-lean `arc/effect-retirement` @ `830fab916`:
  `lean_frontend/docs/2026-08-31_effect-retirement-design.md` (the full
  design note, 2 review rounds: authored, fresh-eyes reviewed
  RATIFY-WITH-AMENDMENTS, amendments applied).
- lem-lean `review/backend-quality` @ `0962814`:
  `doc/lean-backend/2026-08-31_backend-quality-review.md` (the backend
  quality review that shaped the arc's fix-first slice).

## 1. What is being retired, and the contract you get

The Lean port of the Cerberus C semantics (cerberus-lean
`lean_frontend/`) is generated from shared `.lem` sources by this
repository's Lean backend. The port's proof-trust story currently rests
on exactly one axiom: `LemLib.runEffectful : (Unit → BaseIO α) → α`
(`lean-lib/LemLib.lean:54`), the effect-erasure boundary mirroring the
OCaml model's mutable ambient state (fresh-symbol counters, tag-table
writes, debug output). It is declared temporal; this arc deletes it.

**The customer contract (the acceptance criterion, gate-enforced at arc
close):** every constant elaborated from the cerberus-lean repository and
from LemLib has axiom cone ⊆ {`propext`, `Classical.choice`,
`Quot.sound`}. This is the universal form (any definition you unfold, not
just designated entry points), derived from: zero `axiom` declarations
across LemLib + generated + hand-written sources after deletion, plus the
existing bans (no `sorry`, no `native_decide`/`ofReduce*`). Entry-point
`#print axioms` probes (including the `desugar` entry applied at
`Main.lean:512`) remain as end-to-end spot checks.

**What survives, explicitly (ruled [USER 2026-08-31]: the bar is every
axiom gone, with classified survivors):** a small allowlist of kernel-opaque,
pure-signature externs that proofs cannot unfold — they cannot make a
false theorem provable; their hazard is confined to the compiled
evaluator, which sits on the declared differential-validation boundary.
Classification, enforced by the arc's gate ratchet:

| Survivor | Class | Disposition |
|---|---|---|
| `CerberusFresh.digest` (content hashing) | pure-in-fact FFI | becomes a kernel-checked `opaque` (the `with_tagDefs` pattern) in slice C2 |
| `CerbUtils` timing/log refs | no-ops | permanent-declared |
| `CerbGlobal` config refs | should be parameters | temporal; mover = post-arc plumbing slice |
| `CerberusImpl` enum registry | genuinely stateful seam | temporal; mover = the reader/supply machinery this arc builds |

If your proofs need any of these four retired sooner (the enum registry
is the one with real state), say so in review — that re-prioritizes the
follow-up slice.

## 2. The mechanism (ruled decisions)

All decisions below carry operator provenance; the full rulings and their
evidence trail are in the cerberus-side note.

**Q1a [USER]: the split.** The original intent was a purely backend-side
transform. Two independent verifications confirmed that is impossible for
the live `fresh_int` clients: every path crosses a monadic higher-order
boundary (`desugM`/`elabM`), where state-passing is not type-preserving
(the reader transform survives closures via partial application; a supply
threading a result out has no analogous repair), and the constant-
expression leg crosses `Eff.exceptM`, which carries no state component at
all. The ratified design:

- **Backend feature — supply lifting** (`declare {lean} supply val`, this
  repo): the state-passing analog of the existing reader lifting
  (`declare {lean} reader val`), modeled on the same pipeline (declare →
  typecheck field → pre-pass fixpoint → threaded emission), with the
  reader's restrictions carried over as fail-closed generation-time
  guards (no instance methods, no infix position, seed discipline) plus
  supply-specific ones. First-order code threads mechanically.
- **Four bounded model accommodations** (cerberus's `.lem`, not this
  repo): a supply field in the elaboration state + mints, the const-expr
  seam, the `symbol.lem` declare swap, and the `erase_loop_control` local
  state monad. These follow a redirect pattern the fork has executed
  twice before with the oracle byte-identical to upstream.
- Honest cost, ruled with eyes open [USER]: the generated **OCaml text**
  changes (the elaboration-state record is shared between targets; the
  diff is manifest-recorded); oracle dynamic **behavior** is preserved
  and differentially gated (obligations O2/O6). The operator's standing
  objective: leaving the OCaml *output* undisturbed is first-class — not
  quite a red line, but extremely important.

**Q1b [USER]: the one order-moved site.** A review-forced site analysis
classified all 19 live elaboration draw sites: 18 preserve the oracle's
symbol-draw order; one (`with_block_objects`, whose const-alias mints
interleave between its body's construct-time and run-time draws) cannot —
oracle symbol numbering moves on inputs mixing const locals with
drawing statements. Ruled: tolerated, gated by a corpus scan sizing the
affected set first, every affected pinned output enumerated and
rebaselined as an adjudicated instrument change (O6); escalate to a
staged pre-slice if the scan shows nontrivial churn.

**Q2 [USER]: single-stream Lean supply.** Lean-side symbol numbering may
shift; the differential lanes are id-canonicalized by design and the full
battery is the check (O3).

**Q3 [USER]: `reader_consumer` rides the arc** — a small companion
backend feature enabling the tagDefs write-loop closure (the global tag
table and its two remaining write externs are deleted; the table is
passed load→seed directly).

**Debug output** [USER]: leaves the semantics cone entirely — the model
returns values, the driver prints.

## 3. What this repo's arc contains (slice L0 first)

A commissioned quality review of this backend (see the review doc)
mandated a fix-first slice before feature work, and the arc pairs the
supply feature with per-declaration fuel budgets (an independent feature
wanting the same release):

- **L0 (fix first):** contextual-keyword fix (the fork's seven annotation
  words are currently hard lexer keywords — a parser regression for all
  lem users on all targets; any new word this arc adds rides the fixed
  grammar); a nine-target golden-hash regression net for non-Lean output;
  clause-grouping unification; the tuple-destructuring `Let_def`
  RHS-duplication fix (a duplicated supply draw would silently fork
  numbering); `integerDiv` mapping fix (`Int.ediv` → `Int.tdiv`,
  mirroring OCaml `Z.div` truncation); non-ASCII char-literal escapes;
  `setChoose` divergence disposition.
- **L1:** supply lifting + `reader_consumer` + fuel budgets, each with
  fail-closed guards and positive/negative tests in `tests/comprehensive`
  (including compiled-code behavioral tests, closing a known coverage
  gap).
- **C1/C2 (cerberus-side):** adoption, accommodation migration, extern
  deletions, driver seeding; then axiom deletion + gate ratchet
  (census tightening, `runEffectful`-reintroduction ban, plant-tested).
- Close: the two-repo pin dance (lem merges first, ff-only; cerberus
  re-pins and re-gates; both on per-merge operator sign-off).

Blast-radius commitments (operator aims for this repo): minimal impact on
non-Lean lem users (L0's regression net makes this structural; the
review's nine-target sweep is byte-identical today except the keyword
defect being fixed); obviously-right Lean output; clean design;
built for upstream lem review.

## 4. What we ask of the refined-cerberus review

1. **Contract sufficiency:** is the universal axiom-census contract (§1)
   what your adequacy/soundness story needs? Is the three-axiom base
   {propext, Classical.choice, Quot.sound} acceptable to your proofs?
2. **Survivor allowlist:** does any survivor in §1's table sit inside
   definitions you will unfold or need to reason about? (They are opaque
   to the kernel — but if your proof architecture needs, e.g., the
   implementation-defined enum choices as a *function of the impl*, the
   registry's retirement should move up.)
3. **Consumption timing:** the contract lands at arc close (after C2 +
   pin dance). If you need an interim guarantee (e.g. "entry cones only"
   before the universal form), name it.
4. **Anything cerberus-shaped we've missed** from where you sit — the
   operator's standing question is whether generic-looking mechanisms
   carry hidden consumer assumptions.

Review responses: file against this document (this repo, branch
`arc/effect-retirement`) or relay via the operator; the cerberus-side
note is the authoritative technical record and will absorb any resulting
amendments through its established review process.

---

# Consumer review: refined-cerberus / cerberus-heaplang

2026-08-31, [AGENT: refined-cerberus orchestrator], written in-place
per [USER 2026-08-31] instruction (the review may be written into the
same note as a suffix). Left uncommitted — your repo, your commit discipline.
Consumer context: cerberus-heaplang holds machine-checked theorems
whose statements quantify over your engine's production entry
(`initial_driver_state`, Driver.lean:435) and whose certification
proofs UNFOLD engine internals (`step_ctx`, the driver round
functions at Driver.lean:273-351, `loadM`/`storeM`/`allocateObject`,
`finalize`/`Driver.hack`). `runEffectful` appears in our cones today
in exactly one way: through the statement, via
`initial_core_run_state`'s `sym_supply` seam (Core_run_aux.lean:395)
— never through a proof step; the fragment provably never reads the
seam. Our audit holds it in a module-scoped boundary (only 2 of 12
modules may carry it), plant-tested both directions.

## A1 — contract sufficiency: YES, and it is exactly our gate

The universal form (every constant's cone ⊆ the classical trio) is
precisely our in-build sweep's allowlist; stronger than we strictly
need and exactly what we want. At the adoption pin our cleanup is
mechanical: boundary deletion + pin re-baselines. One shape question
whose answer we consume STATEMENT-VISIBLY: does the retired entry
land as (a) a pure closed constructor with a seeded supply value, or
(b) a supply-PARAMETERIZED constructor? Both are fine — under (b)
our theorems gain a ∀-supply quantifier, which is free for us
(never-reads-the-seam is already proved) and arguably strengthens
the exported statements. Please state which in the design record so
our re-export is a planned edit, not a discovery.

## A2 — survivors: no re-prioritization needed; one pattern note

None of the four sits inside definitions our proofs unfold in a way
that blocks us. `digest`-as-kernel-checked-opaque (the with_tagDefs
pattern) is a house-proven shape — no objection. The enum registry:
our current fragment and the planned while-arc (authored Core,
scalar ints) never consume impl enum choices — do not move it up on
our account. Note on the no-op/config refs (CerbUtils, CerbGlobal):
these sit ON or NEAR paths we unfold (`current_execution_mode` is
handled in our proofs by opaque case-split today; debug refs adjoin
the stepping path). Their retirement/parameterization likely
SIMPLIFIES our collapse proofs — welcome — but is re-prove work
either way (see A3).

## A3 — timing: no interim guarantee needed; one deliverable requested

We consume at the pin dance like any pin bump; our content-based
priming guard will trip on C1/C2's real semantics changes, which is
it working as designed — we then re-pin deliberately and re-certify.
The request: at the adoption pin, ship (or point us at) the LEAN-SIDE
analog of your OCaml-text manifest — the list of changed/renamed
definitions in the exec cone, specifically anything in: the entry
constructors (`initial_driver_state`/`initial_core_run_state`), the
driver round path (Driver.lean:273-351 today), `step_ctx`'s cone,
the memory ops, and `finalize`/`hack`. Our re-certification is then
scoped, not discovered. Two adjacent flags:
1. **Fuel budgets**: our exported statements carry fuel side
   conditions against `lemDefaultFuel`, and our size accounting
   tracks the current fuel plumbing. If per-declaration budgets
   change the default-fuel semantics of already-generated functions
   (rather than being opt-in annotation only), that is
   statement-visible for us — please classify.
2. **tagDefs plumbing**: our production theorems pin `drive`'s
   tagDefs argument (`fmapEmpty`, a registered seam with an rfl
   discharge). If reader_consumer/table-deletion changes the
   signature of `drive` or the entry, we re-export once — again,
   just tell us the final signature.

## A4 — consumer assumptions worth making explicit non-goals

1. **Entry purity**: the production entry must remain a pure,
   termination-checked, CLOSED constructor (modulo the supply
   parameter under shape (b)) — we quantify over it verbatim; any
   IO-flavored wrapper reintroduces the class of thing this arc
   deletes.
2. **Sequential-path determinism**: our production equation rests on
   proved singleton step lists + `runND` collapse on the positive
   sequential path. Supply threading is deterministic state and
   should not add ND branch points — please record that as an
   explicit non-goal so a future reviewer can check it cheaply.
3. **Symbol-numbering shifts** (your Q2 and the one order-moved
   site): no objection from us — our theorems are over authored
   Core with directly-constructed symbols; elaboration-side
   numbering is invisible to them today.

Net: RATIFY from the consumer seat, with the A1 shape question and
the A3 deliverable as the two asks. Filed also in our repo's records
at the next slice commit.

---

## Q1b-rescope notice (2026-09-01, appended at L2; addressed to the consumer seat)

[AGENT] (L2 worker, executing the registered R3.1 rider, charter §3.2.)

Three §2 statements above were superseded after this review was
filed and read; if your ratification notes quote them, re-key to the
charter as the correction of record
(cerberus-lean `lean_frontend/docs/2026-08-31_effect-retirement-design.md`
@`64dd6efeb`, §3.6.1 / O2 / O6; C1 adjudication [USER 2026-09-01]):

1. **"The one order-moved site" is now a CLASS.** The S0 corpus scan
   (charter §3.6.1, finding S0-F1) returned NONTRIVIAL: beyond the
   single `with_block_objects` site, an eager-batch movement class
   touches 34/39 speclab dumps, 14/21 corpus pin files, and the
   libc.core pin.
2. **The Q1b escalation clause is SUPERSEDED.** The R2 ruling's
   "escalate to a staged pre-slice on nontrivial churn" did not fire:
   S0-F1 dissolved the staged option's premise. Final ruling
   [USER 2026-08-31]: TOLERATED, full stop; affected oracle outputs
   rebaseline once as an adjudicated instrument change per O2/O6,
   carried by the fork-drift manifest and the C1 upstream-divergence
   enumeration deliverable.
3. **"Behavior preserved (O2/O6)" stands, but read it precisely:**
   oracle dynamic behavior is preserved up to symbol RENAMING;
   affected oracle text diverges from un-forked upstream
   up-to-renaming only. Your §3 item-3 position (elaboration-side
   numbering invisible to your theorems) is unaffected by the
   rescope.
