# Public-readiness review — Lem Lean and Cerberus Lean

2026-09-24. Independent reviewer [AGENT]. Review and remediation plan only;
no implementation, documentation remediation, branch deletion, tagging or
publication is performed by this review.

Reviewed sources:

| Repository | Mainline | Commit |
|---|---|---|
| Lem Lean | `mdd/lean-backend` | `38f87d5fa6b29ec90edfa457faba8a309e32c118` |
| Cerberus Lean | `mdd/cerberus-lean` | `e9f9d049ffaaf005c392495b0f6418d21f4df29f` |

The intended announcement is an **early OathTech fork announcement of the
Lem Lean backend, with Cerberus Lean as its worked example**. Upstream
submission and a stable release are later milestones. The operator reports
that the downstream customer has accepted the semantics; that is useful
adoption evidence, not a general correspondence theorem or independently
repeated customer build in this review.

## A. Public face and claims

### Assessment

The projects offer substantial real functionality: a general Lem-to-Lean
backend, a runtime with tested map/set operations and proved local laws,
explicit reader/supply transformations, structural and fuel-based totality
mechanisms, and a large executable Cerberus consumer. The mainline Cerberus
execution slice has extensive guards and differential evidence. This is
enough substance for an early announcement once the presentation and
newcomer path are repaired. It does not justify a claim of universal
OCaml equivalence, ISO C conformance, arbitrary failure preservation, or
whole-interpreter fuel stability.

Keep both upstream READMEs substantially intact. Amend their small fork
notes and links; put the fork installation instructions, limitations and
evidence in the existing Lean-specific pages. Historical records should
retain their dated observations and quoted rulings. A current landing page
must stop presenting a historical candidate as today's status.

### Graded ledger

Grades: **MUST** before this announcement; **SHOULD** in the cleanup round;
**NICE** useful follow-up; **NOTE** a limit or positive finding, not a demand
to implement a feature. Effort is a reviewer estimate: S = localized change,
M = coordinated change and validation, L = separate development effort.
All findings, grades, remedies and effort estimates are [AGENT] assessments;
quoted operator rulings are marked separately.
Line numbers refer to the commits above. Each remedy is deliberately one
line; the evidence and sequencing follow the ledger.

Derived ledger tally: **11 MUST, eight SHOULD, two NICE and two NOTE**.
The MUST rows are announcement-readiness work, not a request to complete
all deferred semantic features.

| ID | Grade | Repo; location | Finding | One-line fix | Effort |
|---|---|---|---|---|---|
| M1 | MUST | Lem `tests/comprehensive/Makefile:7`, `tests/comprehensive/parity/run.sh:56`; Cerberus `scripts/common.sh:57`, `scripts/capped:20`, `:165` | Tests depend on this machine's absolute cap path and container environment; the cap wrapper can supply prerequisites from an ancestor and its cap enforcement depends on host facilities. | Make the fork build/test path self-contained, document supported cap/toolchain setup and fallback behavior, and remove required private Git redirects. | M |
| M2 | MUST | Cerberus `lean_frontend/README.md:65`, `Makefile:371`, `lean_frontend/lakefile.toml` | The quickstart omits switch creation/fork Lem pinning and native-object compilation, references an unshipped parent `env.sh`, and uses a shared-prefix install; direct CLI examples omit the required panic environment. | Publish and execute one fresh-clone recipe with pinned fork Lem, local switch/runtime prefix, native objects, `LEAN_ABORT_ON_PANIC=1` and one C result. | M |
| M3 | MUST | Lem `doc/lean-backend/README.md:26`, `doc/manual/backend_lean.md:12`; both root fork notes | The backend quickstart stops before checking its generated example; the manual's useful Lake/version instructions are disconnected from that walkthrough, and upstream opam installation can be mistaken for fork installation. | Connect explicit fork branch/revision installation to the existing manual's Lake recipe and finish the quickstart with a checked result and tested toolchain versions. | M |
| M4 | MUST | Lem `doc/lean-backend/README.md:62`, `doc/manual/backend_lean.md:5`, `src/lean_backend.ml:5924` | The unconditional no-`sorry` promise is false: a target representation emits `(sorry : Nat)` successfully. | Qualify the promise everywhere and explicitly document/gate trusted target representations, or remove this escape in a separately validated fix. | S |
| M5 | MUST | Lem `doc/lean-backend/README.md:55`, `DESIGN.md:334`, manual `:229`; `lean-lib/LemLib.lean:167` | The front page promises failure/parity more broadly than the implementation: pure failures can disappear, ordinary panics can return defaults, and byte strings differ. | Put the failure-erasure, panic-environment, byte/Unicode, partial-definition and fuel-propagation limits on the backend front page with the exact supported claim. | S |
| M6 | MUST | Cerberus `lean_frontend/DESIGN.md:113`, `:157`, `VALIDATION.md:16`, `:722`, `:893`, `:1050`; supported profile `:19` | Current-facing documents disagree with the implemented fuel/boundary state, show an old entry-point arity, and retain outstanding September 6 review/adoption/landing exits. | Reconcile the current pages against the registers and landed records, and label the September 6 profile as historical or replace it with a current profile. | M |
| M7 | MUST | Cerberus root `README.md:7`, frontend `README.md:118`, `VALIDATION.md:139`; `scripts/exec_baseline.txt`, `upstream_oracle_differences.json` | “Every corpus” is too broad; 106 minimal rows and five pristine differences are stale; baseline rows are not all agreements. | Use dated, revision-bound counts with agreements separated from exclusions and differences, and limit the root claim to the documented corpora. | S |
| M8 | MUST | Lem `LICENSE:38`, `README.md:200`, `lean-lib/LemLib.lean:7`, `:293`; `ocaml-lib/{pmap,pset}.ml:5` | LemLib calls its AVL code verbatim ports of files carrying OCaml copyright/license notices, but the Lean file has no corresponding notice and the root exception list names the OCaml paths. | Resolve and record the copied-code provenance and applicable notices for the Lean ports, and make the runtime's licensing unambiguous before publication. | M |
| M9 | MUST | Both local `origin/HEAD`; Cerberus Lake URL/revision; root clone/install guidance | Public accessibility, default branch and fetchability of the pinned revision have not been verified without local redirects; cached origin HEAD points to `master` in both repositories. | Verify anonymous public clone/fetch and default branches with redirects disabled, then publish explicit fork-branch clone commands. | S |
| M10 | MUST | Cerberus `.gitignore:87` and tracked `lean_frontend/docs/*-evidence/*.tar.gz` | Twenty-one tracked evidence archives remain despite the explicit repository rule excluding evidence archives from commits/pushes. | Remove the current tracked archives under an agreed retention policy while preserving inventories/reproduction recipes, and separately assess already-reachable history. | M |
| M11 | MUST | Lem `doc/lean-backend/DESIGN.md:268`, `:519`, `tests/comprehensive/test_reader_multi.lem:11` | Sorted positional seeding is described, but the closure extent limit and type-correct seed/own-argument slide are not explained in the public contract. | State that seeding affects generated injection sites in the body, does not reseed previously constructed closures, and requires per-seed value checks when positions share types. | S |
| S1 | SHOULD | Cerberus `lean_frontend/TODO.md:8`, `:302`, `:663`, `:715`; Lem `doc/lean-backend/TODO.md:18`, `:33` | Live TODO prose retains retired consumer/enum state, closed pending workers and resolved smaller items; historical and current work are interleaved. | Reconcile active backlog rows, name cerberus-sl as the current consumer, and retain old names only where historically accurate. | S |
| S2 | SHOULD | Both Lean landing pages; Lem root opam/upstream links | New users are not given a direct OathTech issue-reporting route; internal dated records are described as the bug-report mechanism. | Link the fork issue trackers and give a short reproducer/toolchain checklist, separating upstream filing from fork support. | S |
| S3 | SHOULD | Cerberus `.github/workflows/ci.yml:7`, root badges; Lem `.github` absent | Existing badges/workflows are upstream OCaml/CHERI signals; `scripts/ci_lean.sh` exists but is not wired into an in-repo workflow. | Add a fork-specific Lean smoke workflow or prominently identify the badges as upstream-only and link the manual validation record. | M |
| S4 | SHOULD | Cerberus `lean_frontend/docs/upstream-tray/INDEX.md:9`, `:22`; `VALIDATION.md:223` | The index says nothing has been submitted while recording issue 1009 as filed; “filed upstream” is also used as a register criterion for entries backed by drafts. | Normalize each report's dated Draft/Sent/Filed/Closed status and distinguish a prepared report from a filed issue. | S |
| S5 | SHOULD | Lem `doc/lean-backend/DESIGN.md:499`, `:433`; `src/backend_common.ml`, `src/process_file.ml` | The advertised full declare table omits `ground_rep` and `extra_import`; “all mutable emission state” overlooks the registered global callback/side channel. | Complete the vocabulary table and qualify the state-centralization claim using the existing TODO item. | S |
| S6 | SHOULD | Cerberus `scripts/check_lakefile_roots.sh:33`, `:44`; consumer re-pin note §4 | The script sorts with the C locale but runs `comm` under the ambient locale; a review run under en_US.utf8 printed sorting errors yet returned success. | Give sorting and comparison the same locale, propagate comparison failures, and rerun the existing plants under a non-C locale. | S |
| S7 | SHOULD | Both branch/worktree inventories in C below | Many finished branches/worktrees obscure the active product and consume local resources; ancestry alone does not prove that rebased audit evidence is disposable. | Retire only operator-selected merged worktrees/branches after confirming record preservation; keep parked and upstream-PR work explicitly labelled. | S |
| S8 | SHOULD | Lem root `Makefile:109`; `doc/manual/backend_lean.md:223`; Cerberus `scripts/LADDER.md` | Documentation needs a clear distinction between a small reproducible smoke test, the full backend suite and the externally provisioned release ladder. | Document exact commands, prerequisites and expected scope for each tier, including external corpora and cgroup requirements. | M |
| N1 | NICE | Both Lean doc directories | Hundreds of dated records are valuable evidence but a poor first navigation layer. | Add a short current/history index and explicit supersession links without rewriting or deleting historical evidence. | S |
| N2 | NICE | Lem `doc/lean-backend/TODO.md` items 5, 6, 18 | Ott regeneration, emission-state refactoring and declare consolidation remain upstreaming/stability work. | Keep them on the later upstream-submission plan rather than requiring them for this alpha announcement. | L |
| N3 | NOTE | Both root READMEs and Lean landing pages | Fork identity, upstream attribution and AI-led development under Mike Dodds are already stated. | Preserve the attribution and describe additional tool contributions accurately if the provenance text is updated. | S |
| N4 | NOTE | Lem TODO 13; Cerberus `CerbNDFuelProofs.lean`, `VALIDATION.md:870` | Local sufficiency/zero-case laws and ND stability are real; general driver propagation and whole-interpreter stability are not delivered. | Keep this precise limit in announcement-facing claims; no new global proof is required for an accurately scoped alpha. | S |

### Claim corrections that matter

The root Cerberus sentence “across every corpus in the tree” should become
“on the documented differential test corpora.” The current minimal baseline
has **113 rows: 90 MATCH, 18 UB_MATCH, 5 CERB_SKIP** (derived from the tracked
file), rather than the README's 106/85/18/3. The current pristine register
has **seven** `shared-model-fix` cases (derived), rather than five. These
are baseline inventories, not a new run of all those cases.

The latest inspected round-three full report records 39 selected lanes,
`status = passed`, `selection_complete = true`, and `source_unchanged = true`.
Its certification field is, verbatim:

```text
incomplete: reporting/adoption/audit exits require separate evidence
```

That report is at
`cerberus-lean/lean_frontend/docs/2026-09-22_match-pattern-arity-closure-evidence/round3-34ac493f9/report.json`,
with source head `7acc7326b00bdc80c5ee01d3f1184bc3235468ee`. The subsequent
non-document delta to the reviewed mainline is `lean_frontend/lakefile.toml`
and `lean_frontend/test/Unit/MatchPatternArityTest.lean`; later gate reruns
are recorded in the September 23 re-pin note. Do not re-label this earlier
39-lane report as a full run at `e9f9d049f`.

Current implementation facts should replace the older profile: the pending
fuel register is header-only; `VALIDATION.md` itself now counts 62 measured,
13 zero-case and six outside-execution workers. The enum map is explicit
program data; runtime minting's digest is run-state data; frontend digest
operations remain on the native boundary. Memory-value equality and the
timing/log identities are no longer the old opaque/native seams. The
allowlist records ten boundary opaques after enum retirement, while different
parts of VALIDATION still say twelve and sixteen. The September 6 profile's
eight pending workers and outstanding enum/equality migrations are history.
Update the current entry-point examples as well: DESIGN and VALIDATION
still show `initial_driver_state sup top file fs`, while the landed run-state
API takes `initial_driver_state sup top digest file fs`. Check each related
entry's actual signature rather than applying a blind textual substitution
to the const-expression frontend API.

Do not “correct” accurate historical quotes naming refined-cerberus. Update
current-facing statements. In particular, the top of TODO already records
run-digest work, and its item-7 section explicitly says LANDED; neither
should be reported as wholly unaddressed. The stale tail of TODO still names
the enum registry as a remaining seam and refined-cerberus as customer #1.

Lem's front-page limitations should include: Lem theorem/lemma statements
are dropped as comments; assertions are executable checks; recursion is
`partial` unless totality is requested; fuel sufficiency can require explicit
input hypotheses; arbitrary pure failures are not preserved; panic behavior
depends on execution settings; byte/Unicode strings differ; native-int and
fixed-width conversion behavior includes documented intentional deviations.
The two string XFAILs and two ruled conversion deviations are explicitly
listed in `tests/comprehensive/parity/expected_failures.txt`. A green parity
suite includes those expected differences.

Also qualify the map/set “every observable agrees by construction” wording
in Lem DESIGN and LemLib's module comment: mirrored algorithms, finite
parity tests and the delivered local laws support specific claims, not a
general compiler/runtime correspondence theorem. Cerberus DESIGN's blanket
“full verdict sequences” description should defer to the actual lane
sequence/set/projection matrix already described more carefully in
VALIDATION. The latter's “immovable” fork oracle description also needs to
agree with its newer pristine-reference/shared-model doctrine.

The notice finding M8 is a source-provenance discrepancy, not a legal opinion
about relicensing. The upstream copyright and exception notices must be
preserved and the Lean-port classification resolved by the maintainer; do
not announce “the runtime is simply BSD” based only on the top-level default.

## B. Fresh-clone newcomer path

Fresh local clones were created at `worktrees/readiness-lem-lean/` and
`worktrees/readiness-cerberus-lean/` from the reviewed local repositories,
explicitly selecting the fork branches and using `--no-hardlinks`. No
existing working tree was cleaned, reset, regenerated or installed into.
Toolchains/packages already installed on this host are prerequisites of the
adapted tests; installing them from the public Internet is **UNVERIFIED-OFFLINE**.
These tests do not establish an Internet-only clean-machine build.

The adapted Cerberus build ultimately passed its library/executable build
and the README's one-C-program differential test: both engines reported
`Specified(42)`. This establishes a working path after the explicitly
recorded setup deviations; it does not turn the literal README path into
a successful newcomer walkthrough.

All potentially long operations are time-bounded. Lean execution is routed
through Cerberus's `scripts/capped` with `CERB_MEM_MAX=32G`. Heavy builds
were scheduled serially; the execution appendix discloses a brief overlap
with a foreign build and the reviewer's scheduling deviation. A shell-local opam environment is allowed; modifying the
shared switch or installing into its runtime prefix is not performed.

The ordinary Lem `make` initially failed because the unconfigured shell had
no `ocamlbuild`. Merely adding the switch's `bin` directory was insufficient:
the OCaml library tests failed with `dllzarith.so: No such file or directory`.
Using `opam exec --switch=<existing switch> -- make` passed. These are
prerequisite/environment observations, not evidence that a correctly
installed opam dependency set cannot build Lem. The documentation should
teach the complete opam environment rather than rely on a developer's PATH.

The README's `demo.lem` generation command succeeded. It produces Lean
source but the quickstart stops before compiling or evaluating that source;
building LemLib alone does not check `Demo.lean`. The public recipe should
end with a checked/evaluated example in a small Lake package. The manual
already supplies a Lake dependency example and accurately names both Lean
versions; reuse and directly link that material rather than inventing a
competing installation guide.

Portability traps established by source inspection:

- Lem's comprehensive suite and its parity runner default `CAPPED` to
  `/home/dev/projects/cerberus-lean-proj/cerberus-lean/scripts/capped`.
- Cerberus's `common.sh` refuses a normal tool-equipped shell unless
  `GIT_CONFIG_GLOBAL` is nonempty, with instructions to invoke unshipped
  container `scripts/ce` or `scripts/env.sh`.
- `capped` walks ancestor directories and sources the first `scripts/env.sh`.
  Here that supplies the local switch and Git redirects. A successful run
  inside this container is therefore not proof that the public recipe is
  independent of the container.
- Routing through `capped` does not by itself guarantee a cap on every
  host: source inspection shows direct cgroup-v2 handling, a user-systemd
  fallback, and a loud **uncapped** fallback when `systemd-run` is absent.
  A machine with `systemd-run` but no working user bus can fail instead.
  Document the supported host/prerequisites and this distinction; the
  review's 32G cap is not a measured minimum-memory requirement or a
  certification of other operating systems.
- Cerberus's Lake executable links `native/md5.o`; `lean-prelude-src` does
  not build it. The README omits `make lean-native-obj`; `make lean-build`
  does include that prerequisite. The cold build reproduced the missing
  object link failure; the native-object target followed by the full
  library/executable build succeeded.
- Cerberus's documented `dune install cerberus-lib` has no local prefix,
  contradicting its own updated working instructions. With a shared switch
  this would overwrite the runtime used by other checkouts; the review does
  not execute that command against the shared switch.
- Direct `cerberus-lean --batch ...` invocations require
  `LEAN_ABORT_ON_PANIC=1`; the driver refuses startup without it. The scripts
  supply it, but the public direct-execution examples do not say so. The
  direct review probe returned exit 2 without it and exit 0 with the expected
  `Specified(42)` verdict when it was supplied.
- `check_fork_drift.sh` still has an absolute fallback to this container's
  upstream generated tree and prints a private local-mirror remote recipe.
  A clean external clone must provision the reference explicitly.
- Full validation needs separately provisioned CN/libxml2 sources and the
  independent pristine oracle, and a delegated cgroup-v2 environment for
  `release.py`. Those are not prerequisites for a basic Lem demonstration
  and should not be mixed into its installation instructions.
- Standalone Lem packages pin Lean 4.28.0; Cerberus pins 4.32.2 and consumes
  LemLib at the same Lem revision. Lake rebuilds that dependency under the
  consumer toolchain. State this tested pairing rather than implying one
  universal Lean version.

Executed command results and selected verbatim outputs are in the execution
appendix. A failed reviewer probe or capture is identified separately from
a product failure; no result is inferred from a truncated run.

## C. Repository and evidence hygiene

The container is not the product repository. Its `deps/`, old prototype,
retired verification checkout and existing scratch directories do not enter
a normal clone of either fork. Do not delete them to make a public tree
look clean. Classify actual tracked files separately from local worktrees.

Derived inventory before this review: Cerberus has 47 local branches and
16 registered worktrees including its main checkout; Lem has 10 local
branches and three registered worktrees including main and `deps/lem-pinned`.
The requested “16 worktrees” is thus Cerberus's count, not the two-repository
total. The new review worktree and two scratch clones are additional.

Cerberus's tracked evidence archives total **21 files / 21,888,265 bytes**.
The largest two are `2026-09-22_match-pattern-arity-rereview-evidence/pristine-captures.tar.gz`
(8,384,640 bytes) and `2026-09-22_run-digest-audit-evidence/pristine-captures.tar.gz`
(8,380,976 bytes). This conflicts with the explicit `.gitignore` policy:

> [USER 2026-09-06]: such archives are not to be git-committed and will not be pushed; what matters is that runs can be reconstructed

The ruling is the one recorded in `.gitignore`; the ignored pattern
does not untrack an already committed file. Removing archives at HEAD does
not remove their blobs from history. The history inventory walked
**all local refs**, then separately checked membership in the reviewed
mainline's object closure. These scopes must not be conflated:

| Blob path | Bytes | Reachability at review (derived) |
|---|---:|---|
| `lean_frontend/docs/validation-foundations-repair-evidence/full.tar.zst` | 80,376,450 | Other local refs only; not reviewed mainline history |
| `lib/vellvm/archive/llvm-2.6z.tgz` | 79,608,262 | Other local refs only; upstream-era archive |
| `lean_frontend/docs/validation-foundations-repair-evidence/interrupted-full.tar.zst` | 74,842,295 | Other local refs only; not reviewed mainline history |
| Historical `tests/libc/libc.core` blob | 48,326,282 | Other local refs only; not the current fixture |
| `webcerb.symbolic` | 48,127,164 | Reachable in reviewed mainline history |
| `webcerb.concrete` | 47,988,556 | Reachable in reviewed mainline history |
| `lean_frontend/docs/2026-09-21_sc-prototype-evidence/atomic-surface/component-evidence.tar.gz` | 44,862,601 | Other local refs only; parked SC work |
| `lean_frontend/docs/validation-foundations-evidence/expanded-instruments.tar.gz` | 40,092,033 | Other local refs only |

These are Git blob byte sizes before Git's own compression, not additive
clone-transfer sizes or the expanded contents of the archives. The current
`tests/libc/libc.core` is 4,188,542 bytes and is a deliberate pinned semantics
fixture, not an accidental executable to delete. A normal clone may fetch
multiple advertised branches, but this offline inventory does not establish
which local branches/blobs are advertised publicly.

Inspection method: `git rev-list --objects --all`, followed by
`git cat-file --batch-check='%(objectname) %(objecttype) %(objectsize) %(rest)'`
to classify/size blobs, and comparison with the IDs from
`git rev-list --objects mdd/cerberus-lean`. The fixture's current size came
from `git ls-tree -l HEAD tests/libc/libc.core` (verbatim):

```text
100644 blob f3ae30f1ddd95f5ad8e3d9f10634c23b4e9ece48 4188542	tests/libc/libc.core
```

Do not attribute inherited upstream archives to this fork's cleanup debt.
Do not rewrite public history as routine cleanup. Decide archive retention
and any exceptional history rewrite separately, with consumer pins protected.

Lem's one current tracked archive is the inherited
`manual/hevea-1.10.tar.gz` (322,256 bytes). No analogous new evidence-archive
problem was found there.

A relative-Markdown-link scan found no missing path target in the designated
public entry pages or in Lem's tracked Markdown. Cerberus had 18 raw scan
candidates: 12 deliberately unavailable historical logs already disclosed
by the evidence README, five broken relative links in a copied historical
profile, and one regex inside a code sample (false positive). This is a
path-existence scan, not an external URL/anchor validator. Preserve the
missing-log disclosure; fix navigation or mark historical copies clearly.

The upstream tray contains 45 numbered Cerberus reports, two Lean reports,
one Lem report and one OCaml report: **49 total**, derived by file inventory.
One is explicitly recorded filed (Cerberus #1009), 48 are draft/record-only
items, and no separate Sent-but-unfiled state is established by the local
records. These are local documentary statuses, not live GitHub verification.
Index text claiming “nothing here has been submitted” contradicts its own
filed entry; conditional prose such as “the filed issue carries” is not
evidence of filing. The historical assertion that #1009 was open in August
must retain its date or be rechecked.

Branch classifications and exact worktree inventory follow below. “Merged”
means ancestor of the reviewed mainline, not permission to delete. Rebased
audit branches may not be ancestors even when their findings were copied
into mainline; preserve unique evidence first.

## D. Trust story and enforcement

The acceptance of a semantics by a reasoning customer is distinct from a
compiler-correctness claim. Keep three layers explicit: shared Lem input;
kernel-checked Lean definitions/local theorems; observed native behavior.
No existing gate proves the equality of all three on arbitrary programs.

**Current-head execution evidence:** the adapted fresh Cerberus clone's
`scripts/test_unit.sh` returned zero (354.86 s), with 15 unit executables
passing and the subsequent gates/self-tests completing. This includes the
axiom/sorry, purity/totality, fuel forms and hypotheses, failure-reach,
source-sync, fork-drift and fixture checks. The fresh clone initially lacked
`upstream/master`; the fork-drift gate correctly failed. For the successful
run that ref was explicitly fetched from the local mirror and
`CERB_UPSTREAM_TREE` pointed to the existing pristine generated tree,
read-only. This is not a fresh public provisioning or rebuild of that oracle.
The full release ladder, external-corpus lanes and a fresh customer build
were not rerun. Release-runner/observation instrument plants passed within
the unit script; those are not substitute full-ladder results.
Lem's `make nonlean-regress` also returned zero: 893 artifact rows and
216 exit-code rows across nine emitters matched the committed goldens.
This includes expected error exits in the reference corpus; it is output
invariance evidence, not a claim that every input succeeds on every target.

| Claim | Implementation / enforcement | Exact limit |
|---|---|---|
| Handwritten source matches generated copies | `tools/check_handwritten_sync.sh`, `handwritten_copy.manifest` | Source-copy equality; binary freshness additionally needs the build and driver stamp. |
| Generated input/output identity | `tools/check_lem_sync.sh`, `tools/check_driver_fresh.sh` | Hash/staging checks, not correctness of Lem translation. |
| No added axioms / no `sorry` on checked consumer surface | `scripts/check_theorem_axioms.sh`, `check_sorry_token.sh` | Recursive source scans, restricted proof methods and entry-cone probes; do not generalize to arbitrary user target reps. |
| Native boundary inventory | `check_theorem_axioms.sh`, `unsafebaseio_allowlist.txt` | Pins the boundary population, not logical/native equivalence. |
| Execution totality and purity discipline | `check_exec_totality.sh`, `check_exec_purity.sh`, `TotalityProofTest.lean` | Named execution-slice scans and probes; frontend and excluded seams have stated limits. Totality script defaults to reporting unless `ENFORCE=1`; the unit caller enforces it. |
| Fuel is explicit and obligations have the intended shape | `check_no_fuel_numerals.sh`, `gen_fuel_parametricity.py --check`, `check_fuel_forms.sh`, `fuel_hypotheses.txt` | Numeral scan is a syntactic speedbump; measured laws require their hypotheses; zero-case equations alone do not prove propagation. |
| Proof carriers are included and built | `check_lakefile_roots.sh`, `common.sh:build_lean`, `check_fuel_forms.sh` | Names and freshness/build checks; the roots checker alone builds nothing. |
| Failure-site inventory | `check_failure_reach.sh`, `failure_reach_register.txt` | Reviewed reachability classes and plants, not a universal failure-preservation theorem. |
| Fork source drift and pristine behavioral differences | `check_fork_drift.sh`, `fork_drift_manifest.txt`, `test_upstream_oracle.py`, `upstream_oracle_differences.json` | Missing upstream prerequisites fail by default; only explicit `CERB_FORK_DRIFT_DEV_SKIP=1` permits a prominently labelled development skip, which is not a pass. |
| Printed native observations agree on measured rows | `test_exec.sh` and LADDER lanes, shared `observations.py` | Specified sequence/set projections; exclusions, XFAILs, timeouts and registered differences are not agreements. |
| The release selection completed | `release.py`, `ci_lean.sh`, `scripts/LADDER.md` | Exact run/source identities; a selected subset or historical run does not certify a different head. |
| Lem's non-Lean outputs do not regress on the checked corpus | `make nonlean-regress`, comprehensive `lean-invariance` | Golden/corpus evidence, not a proof for every source or emitter. |
| General byte-string parity / arbitrary strict-failure correspondence / whole-driver fuel stability | **No delivered general gate or theorem establishes these claims** | Keep explicit limitations; passing examples and local laws cannot substitute for them. |

The preserved upstream CI badges are not evidence for the Lean rows. A
manual `ci_lean.sh` entry is useful, but not an automatically executing
GitHub workflow. This can remain a documented manual process for an alpha;
the badge must not imply otherwise.

The roots-checker self-test was also run under `LC_ALL=en_US.utf8`.
`comm` printed sorting errors, but the script returned zero and reported
all three planted faults detected plus a green baseline. This confirms
the locale/error-propagation defect S6; it does not establish that one of
those three faults was missed.

## E. Lem mechanisms, upstream distance and remediation plan

### Mechanism coverage

The source implements the core mechanisms advertised by DESIGN: reader and
reader-consumer lifting, N-ary seeding, supply threading, ambient fuel,
measured fuel (including hypotheses), structural recursion, point-free
tail hoisting, derived size/comparison/Inhabited instances, target mappings,
reserved-name checks, unsupported-construct refusal, and rejection of the
retired `effectful` annotation. The comprehensive tests include positive,
negative and non-Lean invariance witnesses for these families. Fuel with
reader lifting in truly mutual blocks is present at the reviewed Lem head.
The source is `src/lean_backend.ml`, not a separate `src/backend/` directory.

This is a mechanism-to-source/test review, not a proof of correctness of
the 8,000-plus-line backend. Two omissions in the purported full vocabulary
table are `ground_rep` and `extra_import` (implemented in the parser/backend
pipeline and mentioned elsewhere). The state-centralization description
should acknowledge `Backend_common.on_cr_simple_applied` and the
`process_file.ml` side channel already registered in TODO item 6.

Representative cross-checks (source lines at the reviewed Lem revision;
test paths are under `tests/comprehensive/`):

| Mechanism in DESIGN | Implementation | Standing witness / qualification |
|---|---|---|
| Reader lifting, extern consumers and N-ary seeds | `src/lean_backend.ml:542`, `:1175`, `:3175`, `:4464` | `test_reader_consumer.lem`, `test_reader_multi.lem`; extent/positional documentation gap M11 |
| Supply threading and composition restrictions | `src/lean_backend.ml:1250`, `:2622`, `:5651` | `test_supply.lem`, `test_supply_multi.lem`, `negative/neg_supply_*` and parity probes |
| Ambient/measured fuel, hypotheses and mutual reader composition | `src/lean_backend.ml:649`, `:739`, `:4383`, `:4784` | `test_fuel_param.lem`, `test_fuel_measure*.lem`, `test_fuel_mutual_reader.lem`; general propagation remains TODO 13 |
| Structural recursion and point-free tail hoisting | `src/lean_backend.ml:1090`, `:1898`, `:3260`, `:4253` | `test_structural.lem`, `invariance/inv_function_tails.lem`, capture-refusal probes |
| Derived comparisons and computable sizes | `src/lean_backend.ml:7744`, `:8083` | Instance/comparison tests, `test_fuel_measure_tree.lem`, `invariance/inv_lem_size.lem` |
| Instance priorities and supported failure fallback | `src/lean_backend.ml:7218`, `:7598`; `library/` target reps | `test_instance_priority.lem`; opaque failures and supplied `Inhabited` values do not prove strict failure correspondence |
| Target representations and imports | `src/lean_backend.ml:3503`, `:3957`, `:5879`, `:5924` | `ground_rep` and `extra_import` exist but are omitted from DESIGN's full table; explicit `sorry` escape M4 |
| Retired effects, unsupported constructs and capture refusal | `src/lean_backend.ml:525`, reserved-name checks and `LemUnsupported` handling | `negative/neg_effectful_retired.lem`, `neg_unsupported_*`, `neg_fuel_rep_capture.lem`, `neg_tail_rep_capture.lem` |
| Per-file/invocation emission state | `src/lean_backend.ml:240`, `:417` | `St` exists; broader state-centralization wording needs S5's qualification |

`reader_seed` supplies values at generated call sites within the seed
definition. A function value passed into that definition can already have
captured a reader value through partial application; seeding does not
retroactively rewrite that closure. In addition, the first N parameters are
positional seeds: a missing conceptual seed can slide a same-typed ordinary
argument into the Nth seed position and still typecheck. The September 19
S0.5 consumer record §10 documents this and requires value pins; the public
Lem contract should teach it directly. Existing three-reader tests correctly
use equal-typed readers with different values to expose swaps. The review
also generated an independent closure probe: `captured` calls `enter 99`
with a thunk containing `read_cfg _lemReader_cfg`, while `enter` only applies
its thunk. The emitted code confirms the captured reader is retained.

The no-`sorry` counterexample is a real generation result, not a grep of
historical comments or unreachable set-comprehension rendering. The latter
`sorry` strings in the backend are confined to comment rendering; do not
report them as additional live emission bugs. Cerberus also retains target
reps spelled `sorry` in an excluded concurrency model, which does not imply
that the generated, gated mainline execution slice contains them.

### Upstream distance and publication checks

Against the **locally available** upstream-tracking `master`, Lem has merge
base `3802cb0`, zero upstream-only commits and 220 fork-only commits;
Cerberus has merge base `b9aeedcb4`, zero upstream-only commits and 922
fork-only commits (derived using `git rev-list --left-right --count`). Lem's
diff is 461 files, 48,664 insertions and 258 deletions. This is a substantial
fork affecting shared parser/AST/backend paths as well as adding a target;
the non-Lean regression/invariance checks are important for a later PR.
Current upstream behind-count and merge conflicts are **UNVERIFIED-OFFLINE**;
zero behind a cached local ref is not zero behind today's upstream.

Commands and verbatim output for the cached comparison:

```text
lem-lean$ timeout 10 git rev-list --left-right --count master...mdd/lean-backend
0	220
lem-lean$ timeout 10 git diff --shortstat master...mdd/lean-backend
 461 files changed, 48664 insertions(+), 258 deletions(-)
cerberus-lean$ timeout 10 git rev-list --left-right --count master...mdd/cerberus-lean
0	922
```

[AGENT] The shared parser/AST/library changes create integration-review
risk for upstream even with a zero cached behind-count. Before a later PR,
fetch current upstream into a disposable clone, inspect the shared-path
delta, try the merge there and rerun the non-Lean regression net. A
conflict-free merge would still not establish behavioral compatibility.

Cached origin mainline refs equal the reviewed heads in both repositories.
Both cached `origin/HEAD` refs point to `origin/master`. Neither observation
establishes the current public default branch, visibility or availability of
the dependency commit. Run these from a networked environment without the
workspace redirects (commands are proposed, not executed here):

```bash
GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 GIT_TERMINAL_PROMPT=0 timeout 60 git ls-remote --symref https://github.com/OathTech/lem-lean.git HEAD refs/heads/master refs/heads/mdd/lean-backend
GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 GIT_TERMINAL_PROMPT=0 timeout 60 git ls-remote --symref https://github.com/OathTech/cerberus-lean.git HEAD refs/heads/master refs/heads/mdd/cerberus-lean
GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 GIT_TERMINAL_PROMPT=0 timeout 60 git ls-remote https://github.com/rems-project/lem.git refs/heads/master
GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 GIT_TERMINAL_PROMPT=0 timeout 60 git ls-remote https://github.com/rems-project/cerberus.git refs/heads/master
```

An arbitrary commit need not be advertised by `ls-remote`; also perform a
fresh public clone/fetch and `git cat-file -e
38f87d5fa6b29ec90edfa457faba8a309e32c118^{commit}` before relying on the
Cerberus Lake pin. Repeat with the final release pins after remediation.
Use HTTPS in public instructions and explicitly choose the fork branch.

For example, from a new empty directory outside this container, with both
destination names absent (also **UNVERIFIED-OFFLINE**):

```bash
GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 GIT_TERMINAL_PROMPT=0 timeout 180 git clone --branch mdd/lean-backend https://github.com/OathTech/lem-lean.git public-lem-check
timeout 10 git -C public-lem-check cat-file -e 38f87d5fa6b29ec90edfa457faba8a309e32c118^{commit}
GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 GIT_TERMINAL_PROMPT=0 timeout 180 git clone --branch mdd/cerberus-lean https://github.com/OathTech/cerberus-lean.git public-cerberus-check
timeout 10 git -C public-cerberus-check cat-file -e e9f9d049ffaaf005c392495b0f6418d21f4df29f^{commit}
```

### Remediation order and acceptance conditions

1. **Make the newcomer path reproducible (M1–M3, M9).** One contributor
   follows each fork guide in a directory outside this container ancestry,
   with no copied `_build`, `.lake`, generated tree, `_opam` symlink or
   private Git configuration. Install the stated prerequisites, build Lem,
   generate/build/evaluate its demo, run its comprehensive suite, then build
   Cerberus and execute one C program. Every necessary command must appear
   in the guide. Public network/toolchain availability must be checked.
2. **Reconcile public claims (M4–M7, M11; S1, S2, S4, S5).** Maintain one
   current supported-profile page and dated evidence pointers. Include a
   short limitation list on Lem's front page, correct the changed API
   signatures/counts/boundaries, and make the issue-reporting route visible.
   No large semantic feature is required merely to remove an overclaim.
3. **Resolve notices and artifact policy (M8, M10; S7).** Record provenance,
   retain required notices, remove disallowed current evidence archives with
   reproducible summaries, and classify historical blobs/branches without
   automatic deletion or history rewriting.
4. **Validate the final candidates.** Run Lem's standalone runtime,
   comprehensive suite and non-Lean regression net; run the affected
   Cerberus gates and documented smoke path. For any renewed full-ladder
   claim, run the complete selected ladder on frozen final sources and
   explicitly identify unavailable reporting/adoption exits. Check that no
   gate silently relies on private corpora, hidden opam pins, warm objects or
   skipped upstream checks. Preserve the exact commands, versions and heads.
5. **Publish the alpha deliberately.** Review the small root fork notes and
   announcement wording against the completed evidence, then obtain the
   operator's separate publication authorization. The review itself neither
   authorizes nor performs a push, tag, release or upstream message.

### Announcement checklist

- [ ] All MUST findings closed, with a dated final two-repository pin pair.
- [ ] Fresh public clone succeeds with redirects disabled and correct fork branches.
- [ ] Fork Lem install path and Lean/OCaml version matrix are explicit.
- [ ] Generated Lem demo is compiled/evaluated; Cerberus runs one C example.
- [ ] Limitations include strings, pure failures, default partial recursion,
      native seams, fuel scope and unsupported Cerberus concurrency/filesystem modes.
- [ ] Headline counts carry dates, pins and agreement/exclusion distinctions.
- [ ] Licensing/provenance notices for the Lean runtime are resolved.
- [ ] Evidence artifacts and public issue statuses match their stated policy.
- [ ] Fork issue links work; badges are clearly scoped.
- [ ] Public dependency commits, branch visibility and anonymous fetch verified.
- [ ] Prefer coordinated, annotated prerelease tags such as
      `lean-backend-v0.1.0-alpha.1` and `cerberus-lean-v0.1.0-alpha.1` after
      cleanup, rather than a stable `v1.0` or an ambiguous upstream-looking tag.
- [ ] Announcement identifies OathTech forks and attributes upstream work;
      any customer statement describes adoption without implying endorsement
      or a universal proof. Upstream notice/PR is a separately authorized step.

No tag matching `*lean*` exists in either local tag inventory (`git tag
--list '*lean*'` returned no output in each). Remote tag availability is
UNVERIFIED-OFFLINE. [AGENT] A coordinated prerelease tag is useful for a
reproducible announcement; it is warranted after the listed cleanup and
validation, not as a certification of today's documentation.

Suggested scope of the eventual announcement: an experimental Lean 4 backend
for Lem, developed primarily with AI agents under human direction, with
Cerberus C semantics as a substantial executable consumer; selected local
proofs and differential tests support the documented profile, and explicit
limitations remain. Avoid “verified compiler,” “all C,” “equivalent by
construction,” “never emits sorry,” “all tests are agreements,” and an
unqualified “axiom-free semantics.”

Candidate root fork notes for the cleanup round (proposed text only; leave
the upstream sections and existing provenance paragraphs in place):

**Lem:** “This fork adds an experimental Lean 4 backend (`lem -lean`) and
its runtime library (`lean-lib/`). See the [Lean backend guide](README.md)
for fork installation, examples, validation and current limitations;
installing the upstream opam release does not install this backend.”

**Cerberus:** “This fork adds an experimental Lean 4 port of the Cerberus
semantics, generated from shared Lem source with handwritten runtime
components and differentially tested on the documented corpora. See
`lean_frontend/README.md` for the supported sequential configuration,
fork-specific build instructions, validation evidence and limitations.
Builds of this fork require the Lem fork identified in that guide.”

When inserted at Lem's root, the guide link above must target
`doc/lean-backend/README.md`; it is relative to this review here. The final
landing pages, not these short notes, carry the detailed limits. No stable
release or general equivalence claim is implied by either note.

### Verdict

**[AGENT] Not ready to announce from the current documentation and newcomer
instructions; ready for a bounded cleanup round leading to an early alpha
announcement.** The obstacles are reproducibility, contradictory public
claims, source notices and artifact/publication hygiene. The existing
implementation and validation work support a useful early release with
honest limits. Completing weak-memory support, general strict-failure
translation, universal fuel propagation or the later upstreaming refactors
is not required for that narrowly stated announcement.

## Inventory appendix — branches and worktrees

The following classifications are [AGENT] recommendations. Commands:

```bash
timeout 10 git for-each-ref --format="%(refname:short) %(objectname:short)" refs/heads
timeout 10 git merge-base --is-ancestor <branch> <fork-mainline>
timeout 10 git worktree list
```

### lem-lean

| Branch | Head | Ancestry / disposition |
|---|---|---|
| `arc/effect-retirement` | `045dcb0` | Merged; candidate-delete branch/worktree after operator review |
| `arc/effects-totality` | `d25f982` | Merged; candidate-delete branch/worktree after operator review |
| `arc/libc-load` | `bd7e2eb` | Merged; candidate-delete branch/worktree after operator review |
| `arc/next` | `f6542f8` | Merged; candidate-delete branch/worktree after operator review |
| `arc/totality-sweep` | `574e326` | Merged; candidate-delete branch/worktree after operator review |
| `cerberus-pin` | `38f87d5` | Keep: mainline / upstream-tracking / active pin |
| `master` | `3802cb0` | Keep: mainline / upstream-tracking / active pin |
| `mdd/lean-backend` | `38f87d5` | Keep: mainline / upstream-tracking / active pin |
| `noodle/backend` | `a02cb6f` | Keep as record; not an ancestor (may be rebased/copied) |
| `review/backend-quality` | `0962814` | Keep as record; not an ancestor (may be rebased/copied) |

Registered worktrees (verbatim `git worktree list` lines, excluding this newly created review worktree):

```text
/home/dev/projects/cerberus-lean-proj/lem-lean                                      38f87d5 [mdd/lean-backend]
/home/dev/projects/cerberus-lean-proj/deps/lem-pinned                               38f87d5 [cerberus-pin]
/home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-arc/fuel-parameter         f6542f8 [arc/next]
```

### cerberus-lean

| Branch | Head | Ancestry / disposition |
|---|---|---|
| `arc/address-space-bound-part-two` | `0457732e1` | Merged; candidate-delete branch/worktree after operator review |
| `arc/allocator-soundness-address-bound` | `e64819de7` | Merged; candidate-delete branch/worktree after operator review |
| `arc/concurrency-landing` | `1349ec56f` | Keep as parked/design record; not mainline-merged |
| `arc/lean-only-outcomes-S0` | `8f8c4dfe7` | Keep as parked/design record; not mainline-merged |
| `arc/next` | `e30810be7` | Merged; candidate-delete branch/worktree after operator review |
| `arc/pristine-oracle-instrument` | `4a23d98aa` | Merged; candidate-delete branch/worktree after operator review |
| `arc/program-data-parameters` | `df85e95b7` | Merged; candidate-delete branch/worktree after operator review |
| `arc/run-digest` | `34ac493f9` | Merged; candidate-delete branch/worktree after operator review |
| `arc/sc-prototype` | `0e6947988` | Keep as parked/design record; not mainline-merged |
| `arc/seam-hygiene` | `a8d00feed` | Merged; candidate-delete branch/worktree after operator review |
| `arc/segment-ladder` | `fcfa8934c` | Keep as parked/design record; not mainline-merged |
| `arc/t5-seal` | `6f321327a` | Keep as parked/design record; not mainline-merged |
| `arc/validation-foundations` | `d607409f9` | Keep as record; not an ancestor (may be rebased/copied) |
| `arc/validation-foundations-concurrency` | `86a2aea54` | Keep as parked/design record; not mainline-merged |
| `audit/allocator-part-one` | `f8222307f` | Keep as record; not an ancestor (may be rebased/copied) |
| `audit/concurrency-design-20260919` | `38d7d2123` | Keep as record; not an ancestor (may be rebased/copied) |
| `audit/concurrency-premerge` | `c0a926707` | Keep as record; not an ancestor (may be rebased/copied) |
| `audit/enum-base-20260920` | `5407597d9` | Merged; keep audit record until preservation confirmed |
| `audit/enum-premerge-20260920` | `880a8ead8` | Keep as record; not an ancestor (may be rebased/copied) |
| `audit/enum-repairs-20260921` | `44e7989af` | Keep as record; not an ancestor (may be rebased/copied) |
| `audit/fuel-forms-carriers` | `bda941a5a` | Keep as record; not an ancestor (may be rebased/copied) |
| `audit/item7-rereview-20260922` | `3e8f7c4bd` | Keep as record; not an ancestor (may be rebased/copied) |
| `audit/item7-round3-review-20260923` | `629aab197` | Keep as record; not an ancestor (may be rebased/copied) |
| `audit/match-pattern-arity-20260921` | `14457f1a0` | Keep as record; not an ancestor (may be rebased/copied) |
| `audit/pristine-oracle-instrument` | `4df08432e` | Keep as record; not an ancestor (may be rebased/copied) |
| `audit/program-data-parameters-S0.5` | `57a2d3bd7` | Keep as record; not an ancestor (may be rebased/copied) |
| `audit/run-digest-20260922` | `97c98bcce` | Keep as record; not an ancestor (may be rebased/copied) |
| `audit/seam-hygiene` | `05d208f45` | Keep as record; not an ancestor (may be rebased/copied) |
| `docs/concurrency-landing-scoping` | `6da619f69` | Merged; candidate-delete branch/worktree after operator review |
| `docs/concurrency-pause` | `b7e45d55e` | Merged; candidate-delete branch/worktree after operator review |
| `docs/concurrency-research-20260920` | `02a6adc90` | Keep as record; not an ancestor (may be rebased/copied) |
| `docs/concurrency-scoping-erratum` | `bb09cb745` | Merged; candidate-delete branch/worktree after operator review |
| `docs/consumer-repin-2026-09-23` | `e9f9d049f` | Merged; candidate-delete branch/worktree after operator review |
| `docs/d2-structural-outcomes-response` | `59dbb603d` | Merged; candidate-delete branch/worktree after operator review |
| `docs/lean-only-outcomes-S0-record` | `bfca41724` | Merged; candidate-delete branch/worktree after operator review |
| `docs/lean-only-outcomes-plan-review` | `0c78635cb` | Merged; candidate-delete branch/worktree after operator review |
| `docs/program-data-parameters-design` | `1c319a40e` | Keep as record; not an ancestor (may be rebased/copied) |
| `docs/run-digest-design` | `4d777218e` | Keep as record; not an ancestor (may be rebased/copied) |
| `docs/tray-44-allocator-division` | `b7b8e4250` | Merged; candidate-delete branch/worktree after operator review |
| `feature/concurrency` | `086d8762d` | Keep as parked/design record; not mainline-merged |
| `fix/match-pattern-arity` | `2b51d2a57` | Merged; candidate-delete branch/worktree after operator review |
| `master` | `b9aeedcb4` | Keep: mainline / upstream-tracking / active pin |
| `mdd/cerberus-lean` | `e9f9d049f` | Keep: mainline / upstream-tracking / active pin |
| `upstream-pr/bswap64` | `c44d30dcf` | Keep: prepared upstream contribution, not mainline-merged |
| `upstream-pr/char-escapes` | `da993e5a0` | Keep: prepared upstream contribution, not mainline-merged |
| `upstream-pr/pp-roundtrip` | `c3d18a49f` | Keep: prepared upstream contribution, not mainline-merged |
| `wip/fuel-parameter-C1-scratch` | `b0f718eda` | Unmerged scratch; candidate-delete only after unique-work inspection |

Registered worktrees (verbatim `git worktree list` lines, excluding this newly created review worktree):

```text
/home/dev/projects/cerberus-lean-proj/cerberus-lean                                                e9f9d049f [mdd/cerberus-lean]
/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-arc/lean-only-outcomes-S0            8f8c4dfe7 [arc/lean-only-outcomes-S0]
/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-arc/sc-prototype                     0e6947988 [arc/sc-prototype]
/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-arc/zero-discrepancy                 e30810be7 [arc/next]
/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/concurrency-design-20260919    38d7d2123 [audit/concurrency-design-20260919]
/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/enum-base-20260920             5407597d9 [audit/enum-base-20260920]
/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/enum-premerge-20260920         880a8ead8 [audit/enum-premerge-20260920]
/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/enum-repairs-20260921          44e7989af [audit/enum-repairs-20260921]
/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/match-pattern-arity-20260921   14457f1a0 [audit/match-pattern-arity-20260921]
/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-audit/run-digest-20260922            97c98bcce [audit/run-digest-20260922]
/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-docs/concurrency-research-20260920   02a6adc90 [docs/concurrency-research-20260920]
/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-docs/program-data-parameters-design  1c319a40e [docs/program-data-parameters-design]
/home/dev/projects/cerberus-lean-proj/worktrees/cerberus-lean-feature/concurrency                  086d8762d [feature/concurrency]
/home/dev/projects/cerberus-lean-proj/worktrees/upstream-pr-bswap64                                c44d30dcf [upstream-pr/bswap64]
/home/dev/projects/cerberus-lean-proj/worktrees/upstream-pr-char-escapes                           da993e5a0 [upstream-pr/char-escapes]
/home/dev/projects/cerberus-lean-proj/worktrees/upstream-pr-pp-roundtrip                           c3d18a49f [upstream-pr/pp-roundtrip]
```

## Execution appendix — review runs

These are review executions in the two scratch clones, not a new full
release certification. The runner wrapped each listed shell command in
`timeout --kill-after=10s <budget> bash -c <command>`, kept stdout/stderr
together as raw bytes, and recorded the child exit status. An empty output
on success is not a missing result. Durations are observations, not build
benchmarks. Absolute paths below identify this review environment and are
not proposed public installation instructions.

### Environment and deviations

The available tools were opam 2.1.5, OCaml 5.4.0, dune 3.23.1 and the
freshly built `Lem 38f87d5`. The checked-in toolchain files select Lean
4.28.0 for standalone LemLib and Lean 4.32.2 for Cerberus. The host already
had those toolchains and opam dependencies. The initial Lem cap wrapper
auto-sourced the ancestor container environment; later probes explicitly
set `CERB_PROJ` and `GIT_CONFIG_GLOBAL` to prevent that implicit setup.

For the adapted Cerberus run, the scratch clone's `_opam` is a symlink to
the existing main checkout's switch. It is used for tools/dependencies;
no packages were installed or upgraded there. `dune install` instead used
the scratch clone's `_build/local-install`. The locally rebuilt Lem was
put first on PATH, with LEMLIB pointing to that same scratch checkout.
The local Git configuration redirects the OathTech (and legacy septract)
Lem URL to the reviewed local repository. The dependency was cloned and
built in the scratch Lake package directory; no existing `.lake` or
generated tree was copied into the fresh clone. Public fetchability is
still UNVERIFIED-OFFLINE.

The Cerberus environment file used by the commands below was:

```bash
export CERB_PROJ="/home/dev/projects/cerberus-lean-proj/worktrees/readiness-cerberus-lean"
export GIT_CONFIG_GLOBAL="/home/dev/projects/cerberus-lean-proj/worktrees/readiness-cerberus-lean/.readiness/gitconfig"
export CERB_MEM_MAX=32G
export DUNE_CACHE=disabled
export PATH="/home/dev/projects/cerberus-lean-proj/worktrees/readiness-lem-lean:$PATH"
export LEMLIB="/home/dev/projects/cerberus-lean-proj/worktrees/readiness-lem-lean/library"
```

The scratch Git configuration was:

```gitconfig
[url "/home/dev/projects/cerberus-lean-proj/lem-lean"]
	insteadOf = https://github.com/OathTech/lem-lean
	insteadOf = https://github.com/septract/lem-lean
[protocol "file"]
	allow = always
```

Reviewer execution caveats: an initial comprehensive-run logger attempted
UTF-8 text capture and failed on byte `0xc8`; no successful exit is claimed
for that lost capture. The replacement captured raw bytes. Its 600-second
run was paused while an unrelated build ran, and the timeout included the
pause. It completed generation, compilation, runtime pins, negative tests
and invariance, then timed out during parity. The remaining parity and
token-gate stages were rerun successfully as a separate command. Thus all
stages were exercised, but there is no claimed uninterrupted green
`make lean` run in this review. The timed-out run's generation/compilation
reused results from the earlier attempt; the standalone library and first
consumer build started without pre-existing build artifacts in the clones.

The first `sorry` reproducer used a reserved Lem name and the first closure
probe used an unsupported annotated seed binder; both were reviewer-input
errors and are explicitly retained as failed probes in the command list.
Corrected probes below establish the findings.

Build scheduling was checked between jobs and the earlier suite was paused
for a foreign build. A later foreign build overlapped the end of the cold
Cerberus build; a 1.44-second native-object/relink command was also mistakenly
launched before acting on that process check. This is a reviewer scheduling
deviation, not product evidence; no foreign process was stopped or changed.
Further heavy testing waited for the foreign build to end.

### Command results

`cwd` is relative to the scratch clone named by the command's prefix;
`versions` also ran in the Lem clone. Commands with a `cerberus-` prefix
ran in the Cerberus clone. The status below is the command's exit status,
not the outer logging helper's status.

**`lem-make-literal`** — cwd `.`; exit **2**; 0.1 s.

```bash
make
```

**`lem-make-provisioned`** — cwd `.`; exit **2**; 48.84 s.

```bash
export PATH=/home/dev/projects/cerberus-lean-proj/cerberus-lean/_opam/bin:$PATH; make
```

**`lem-make-opam`** — cwd `.`; exit **0**; 23.75 s.

```bash
opam exec --switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean -- make
```

**`lem-lean-libs`** — cwd `.`; exit **0**; 3.85 s.

```bash
opam exec --switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean -- env CERB_MEM_MAX=32G /home/dev/projects/cerberus-lean-proj/cerberus-lean/scripts/capped make lean-libs
```

**`lem-runtime`** — cwd `lean-lib`; exit **0**; 10.5 s.

```bash
CERB_MEM_MAX=32G /home/dev/projects/cerberus-lean-proj/cerberus-lean/scripts/capped lake build
```

**`lem-demo`** — cwd `.`; exit **0**; 1.81 s.

```bash
./lem -wl ign -i library/pervasives.lem -lean demo.lem
```

**`lem-sorry`** — cwd `.`; exit **1**; 0.0 s.

```bash
./lem -wl ign -i library/pervasives.lem -lean readiness_sorry.lem && cat Readiness_sorry.lean
```

**`lem-sorry-corrected`** — cwd `.`; exit **0**; 1.04 s.

```bash
./lem -wl ign -i library/pervasives.lem -lean readiness_sorry.lem && cat Readiness_sorry.lean
```

**`cerberus-readme-first-command`** — cwd `.`; exit **2**; 0.1 s.

```bash
opam exec --switch=. -- make prelude-src
```

**`cerberus-readme-env`** — cwd `.`; exit **1**; 0.0 s.

```bash
test -f ../scripts/env.sh; test -f lean_frontend/native/md5.o
```

**`cerberus-test-bare-env`** — cwd `.`; exit **2**; 0.01 s.

```bash
env -u GIT_CONFIG_GLOBAL ./scripts/test_exec.sh tests/minimal/001-return-literal.c
```

**`versions`** — cwd `.`; exit **0**; 0.05 s.

```bash
opam --version; opam exec --switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean -- ocamlc -version; opam exec --switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean -- dune --version; ./lem -v
```

**`lem-shipped-example`** — cwd `.`; exit **0**; 1.73 s.

```bash
./lem -wl ign -lib library -lean -outdir .readiness/example examples/ppcmem-model/bitwiseCompatibility.lem
```

**`lem-seed-extent`** — cwd `.`; exit **1**; 1.87 s.

```bash
./lem -wl ign -i library/pervasives.lem -lean readiness_seed.lem && tail -8 Readiness_seed.lean
```

**`lem-seed-extent-corrected`** — cwd `.`; exit **0**; 1.91 s.

```bash
./lem -wl ign -i library/pervasives.lem -lean readiness_seed.lem && tail -12 Readiness_seed.lean
```

**`lem-comprehensive-byte-safe`** — cwd `tests/comprehensive`; exit **124**; 600.0 s.

```bash
opam exec --switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean -- env CERB_MEM_MAX=32G make lean
```

**`lem-comprehensive-final-legs`** — cwd `tests/comprehensive`; exit **0**; 147.78 s.

```bash
opam exec --switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean -- env CERB_MEM_MAX=32G CERB_PROJ=/home/dev/projects/cerberus-lean-proj/worktrees/readiness-lem-lean GIT_CONFIG_GLOBAL=/dev/null make lean-parity lean-no-sorry-proofs lean-no-fuel-numerals
```

**`lem-generated-checks`** — cwd `lean-lib`; exit **0**; 1.51 s.

```bash
CERB_PROJ=/home/dev/projects/cerberus-lean-proj/worktrees/readiness-lem-lean GIT_CONFIG_GLOBAL=/dev/null CERB_MEM_MAX=32G /home/dev/projects/cerberus-lean-proj/cerberus-lean/scripts/capped lake env lean ../.readiness/DemoCheck.lean && CERB_PROJ=/home/dev/projects/cerberus-lean-proj/worktrees/readiness-lem-lean GIT_CONFIG_GLOBAL=/dev/null CERB_MEM_MAX=32G /home/dev/projects/cerberus-lean-proj/cerberus-lean/scripts/capped lake env lean ../.readiness/SeedCheck.lean && CERB_PROJ=/home/dev/projects/cerberus-lean-proj/worktrees/readiness-lem-lean GIT_CONFIG_GLOBAL=/dev/null CERB_MEM_MAX=32G /home/dev/projects/cerberus-lean-proj/cerberus-lean/scripts/capped lake env lean ../.readiness/example/BitwiseCompatibility.lean
```

**`cerberus-provisioned-ocaml-and-generation`** — cwd `.`; exit **0**; 51.13 s.

```bash
opam exec --switch=. -- bash -c 'source .readiness/build-env.sh; make prelude-src && dune build backend/driver/main.exe cerberus-lib.install && dune install --prefix "$PWD/_build/local-install" cerberus-lib && dune build cerberus.install && make lean-prelude-src'
```

**`cerberus-fork-drift-fresh`** — cwd `.`; exit **1**; 0.06 s.

```bash
opam exec --switch=. -- bash -c 'source .readiness/build-env.sh; ./scripts/check_fork_drift.sh'
```

**`cerberus-provision-upstream-ref`** — cwd `.`; exit **0**; 0.01 s.

```bash
git fetch /home/dev/projects/cerberus-lean-proj/deps/mirrors/cerberus.git master:refs/remotes/upstream/master
```

**`cerberus-lean-readme-build`** — cwd `.`; exit **1**; 183.69 s.

```bash
opam exec --switch=. -- bash -c 'source .readiness/build-env.sh; cd lean_frontend; ../scripts/capped lake build'
```

**`cerberus-native-and-all-roots`** — cwd `.`; exit **0**; 1.44 s.

```bash
opam exec --switch=. -- bash -c 'source .readiness/build-env.sh; ./scripts/capped make lean-native-obj && cd lean_frontend && ../scripts/capped lake build CerberusLean cerberus-lean'
```

**`cerberus-roots-nonc-locale`** — cwd `.`; exit **0**; 0.73 s.

```bash
mkdir -p .readiness/tmp; TMPDIR="$PWD/.readiness/tmp" LC_ALL=en_US.utf8 ./scripts/check_lakefile_roots.sh --selftest
```

**`cerberus-one-c`** — cwd `.`; exit **0**; 2.73 s.

```bash
opam exec --switch=. -- bash -c 'source .readiness/build-env.sh; export TMPDIR="$PWD/.readiness/tmp"; ./scripts/capped ./scripts/test_exec.sh tests/minimal/001-return-literal.c'
```

**`cerberus-unit`** — cwd `.`; exit **0**; 354.86 s.

```bash
opam exec --switch=. -- bash -c 'source .readiness/build-env.sh; export TMPDIR="$PWD/.readiness/tmp"; export CERB_UPSTREAM_TREE=/home/dev/projects/cerberus-lean-proj/deps/cerberus-upstream/ocaml_frontend/generated; ./scripts/capped ./scripts/test_unit.sh'
```

**`lem-nonlean-regress`** — cwd `.`; exit **0**; 106.96 s.

```bash
opam exec --switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean -- make nonlean-regress
```

**`cerberus-direct-without-panic`** — cwd `.`; exit **2**; 0.13 s.

```bash
opam exec --switch=. -- bash -c 'source .readiness/build-env.sh; ./scripts/cerberus --cabs-json tests/minimal/001-return-literal.c > .readiness/return42.json && env -u LEAN_ABORT_ON_PANIC ./scripts/capped lean_frontend/.lake/build/bin/cerberus-lean --batch .readiness/return42.json'
```

**`cerberus-direct-with-panic`** — cwd `.`; exit **0**; 0.09 s.

```bash
opam exec --switch=. -- bash -c 'source .readiness/build-env.sh; LEAN_ABORT_ON_PANIC=1 ./scripts/capped lean_frontend/.lake/build/bin/cerberus-lean --batch .readiness/return42.json'
```

### Selected verbatim output

Only the selected lines are quoted; omitted warnings and full logs are not
represented as an exhaustive transcript. Counts described as derived are
computed inventories rather than text printed by the tools.

From `lem-make-literal`:

```text
ocamlbuild -use-ocamlfind -cflags -g main.native
make[1]: ocamlbuild: No such file or directory
make[1]: *** [Makefile:7: all] Error 127
make: *** [Makefile:222: build-lem] Error 2
```

From `lem-make-provisioned`:

```text
Error: I/O error: dllzarith.so: No such file or directory
```

From `lem-runtime`:

```text
Build completed successfully (39 jobs).
```

From `lem-sorry-corrected`:

```text
def  observed    :  Nat := (sorry : Nat)
```

From `lem-seed-extent-corrected`:

```text
def  read_cfg (_lemReader_cfg : Nat)  (u : Unit)  : Nat := _lemReader_cfg
def  enter  (seed : Nat) (thunk : Unit → Nat)  : Nat :=  thunk  ()
def  captured (_lemReader_cfg : Nat)  (u : Unit)  : Nat :=  enter (  99)  (fun ( _ : Unit) => ( read_cfg _lemReader_cfg)  ())
```

From `lem-generated-checks`:

```text
42
7
```

From `lem-comprehensive-byte-safe`:

```text
=== Generation: 56 passed, 0 failed, 0 skipped ===
Build completed successfully (173 jobs).
  OK (leg 1): panic prints the Incomplete Pattern message, then continues with default
  OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1
  OK: compiled draw sequences hold
  OK: compiled consumer injection holds
  OK: compiled N-ary seed injection holds
  OK (leg 1): two sufficient fuels agree; insufficient gives the declared sentinel; callee starts from the full ambient
  OK (leg 2): loud exhaustion at an insufficient runtime fuel fail-stops (exit 134)
  OK: compiled fuel x reader x mutual composition holds
```

From `lem-comprehensive-final-legs`:

```text
  OK: 11 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
  OK: 260 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
```

From `cerberus-readme-first-command`:

```text
[ERROR] The selected switch /home/dev/projects/cerberus-lean-proj/worktrees/readiness-cerberus-lean is not installed.
```

From `cerberus-test-bare-env`:

```text
env not loaded: run via scripts/ce or source scripts/env.sh
```

From `cerberus-provisioned-ocaml-and-generation`:

```text
[STAMP] recording lem-sync content stamp
check_lem_sync: recorded ocaml_frontend/lem_sync.sha256 (src 20c5b3a382ed464ba28ee42d40950af3d11f454050cb80eaaf280f00bc20b1f7, gen 77527ca73a3c79a836a7027062cc38aa1252c1e1c553d0a5c8d60a1d6ef8aa38)
check_lem_sync: OK (src 20c5b3a382ed464ba28ee42d40950af3d11f454050cb80eaaf280f00bc20b1f7, gen 77527ca73a3c79a836a7027062cc38aa1252c1e1c553d0a5c8d60a1d6ef8aa38)
[COPY] 49 hand-written Lean files (lean_frontend/handwritten_copy.manifest) into [lean_frontend/generated]
check_handwritten_sync: OK (49 hand-written files byte-identical to lean_frontend/generated/; manifest lean_frontend/handwritten_copy.manifest)
[STAMP] recording Lean lem-sync content stamp
check_lem_sync: recorded lean_frontend/lem_sync.sha256 (src 20c5b3a382ed464ba28ee42d40950af3d11f454050cb80eaaf280f00bc20b1f7, gen f4893e95ac3462defae87f737580b172f4e4e1cf35941d5be07edd82c8df808e)
```

From `cerberus-lean-readme-build`:

```text
clang: error: no such file or directory: 'native/md5.o'
error: build failed
```

From `cerberus-native-and-all-roots`:

```text
Build completed successfully (395 jobs).
```

From `cerberus-fork-drift-fresh`:

```text
check_fork_drift: no 'upstream/master' ref in this checkout.
check_fork_drift: FAIL — missing upstream ref 'upstream/master' (fail-closed; the development opt-in is CERB_FORK_DRIFT_DEV_SKIP=1)
```

From `lem-nonlean-regress`:

```text
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
```

From `cerberus-one-c`:

```text
check_lem_sync: OK (src 20c5b3a382ed464ba28ee42d40950af3d11f454050cb80eaaf280f00bc20b1f7, gen 77527ca73a3c79a836a7027062cc38aa1252c1e1c553d0a5c8d60a1d6ef8aa38)
[1/1] MATCH 001-return-literal: VAL:{value: "Specified(42)", stdout: "", stderr: "", blocked: "false"}
SUMMARY: total=1 match=1 ub_match=0 ub_diff=0 mismatch=0 fail=0 crash=0 fuel=0 lean_error=0 timeout=0 hang=0 cerb_skip=0 cerb_floor=0 cerb_inconsistent=0
```

From `cerberus-direct-without-panic`:

```text
cerberus-lean: refused — LEAN_ABORT_ON_PANIC is not set: a Lean panic! (this port's fail-stop mirror of every OCaml failwith/assert/uncaught exception) would print and then CONTINUE with a default value, converting a crash into a verdict; set LEAN_ABORT_ON_PANIC=1 (every harness does: scripts/common.sh run_cerberus_lean; see VALIDATION.md, zero-discrepancy Z2-FL-03)
```

From `cerberus-direct-with-panic`:

```text
Defined {value: "Specified(42)", stdout: "", stderr: "", blocked: "false"}
```

From `cerberus-unit`:

```text
check_handwritten_sync: OK (49 hand-written files byte-identical to lean_frontend/generated/; manifest lean_frontend/handwritten_copy.manifest)
Total: 15 passed, 0 failed
check_theorem_axioms: hand-written axiom census OK (0 axioms — the arc-17 S2b end state)
check_theorem_axioms: generated-tree census OK (219 files: 0 axioms, boundary-opaque population = the 10 registered rows exactly-once (incl. CerbFuel.fuelExhaustedLoc), 0 unsafeCast)
check_theorem_axioms: C2 ratchet OK (413 files scanned recursively: 0 axioms, 0 runEffectful, seam population = the 19 pinned path-qualified counted rows exactly incl. the extern class; lem tests/ scaffolds asserted outside the surface)
check_theorem_axioms: D14 grep-ban OK (no native_decide/bv_decide in 1 tree(s) + 49 hand-written seam files + LemLibTest.lean)
check_theorem_axioms: C2 entry census OK (9 entries, every cone ⊆ [propext, Classical.choice, Quot.sound])
check_theorem_axioms: mem-scale S1 leg OK (6 C1/C3 equality theorems, every cone ⊆ [propext, Classical.choice, Quot.sound])
check_theorem_axioms: FUEL arc leg OK (63 contract lemmas — generated _zero, runner leaves/parametricity, ∀-fuel exemplar, measured obligations, fail-stop propagation, and six-worker ND stability, every cone ⊆ [propext, Classical.choice, Quot.sound])
check_theorem_axioms: OK (effect-retirement C2 bar: zero axiom declarations anywhere; entry cones ⊆ the standard three)
check_sorry_token: OK (321 files scanned comment-stripped — generated 219, hand-written+test 67, LemLib 35; 0 sorry tokens)
Ran 25 tests in 0.501s
OK
Ran 3 tests in 0.619s
OK
Ran 16 tests in 4.288s
OK
Ran 5 tests in 0.003s
OK
Ran 5 tests in 0.422s
OK
check_no_fuel_numerals: SELFTEST OK (26 plants red with the declared label — F1-F6 and A1-A3; E5 indirection a recorded known gap; unplanted set green)
check_no_fuel_numerals: OK (328 files scanned comment-stripped; no lemDefaultFuel/driverFuel/ndDefaultFuel, no LemFuel instance, no literal fuel (F1-F6), no address-space-top literal (A1-A3); allowed Main.lean sites seen: 6 of 6 (hand-written + generated copy))
check_lakefile_roots: SELFTEST OK (3 plants red, baseline green)
check_lakefile_roots: OK (218 roots = 218 generated modules + the exe root Main; 85 auxiliary modules listed as roots — names only; every carrier is built by check_fuel_forms.sh)
  PLANT OK   [P1 measured->ambient reachable (step_eval_pexpr)] -> check_fuel_forms: FAIL — fuel'd worker(s) REACHABLE from drive with an opaque (fail-open) exhaustion, not in /home/dev/projects/cerberus-lean-proj/worktrees/readiness-cerberus-lean/scripts/fuel_forms_pending.txt:
  PLANT OK   [P2 stale pending pin (many_run_lemFuel is MEASURED, not reachable-ambient)] -> check_fuel_forms: FAIL — pending register row(s) no longer a reachable ambient worker (stale pin; edit the register):
  PLANT OK   [P3 measured obligation with sorryAx in its cone] -> check_fuel_forms: FAIL — measured obligation(s) with an axiom cone outside [propext, Classical.choice, Quot.sound] (or no proof constant):
  PLANT OK   [P5 phantom pending-register row] -> check_fuel_forms: FAIL — pending register row(s) no longer a reachable ambient worker (stale pin; edit the register):
  PLANT OK   [P8 register row of a measured-under-hypothesis worker deleted (CerbMem.sizeofCtype)] -> check_fuel_forms: FAIL — worker(s) MEASURED under a hypothesis with no reviewed register row for that exact hypothesis in /home/dev/projects/cerberus-lean-proj/worktrees/readiness-cerberus-lean/scripts/fuel_hypotheses.txt (worker TAB hypothesis):
  PLANT OK   [P9 stale register row (hack under 0 < k — hack IS measured, under CerbCoreShape.IsValuePexpr pexpr1, not under this)] -> check_fuel_forms: FAIL — hypothesis register row(s) whose worker is not MEASURED under that exact hypothesis (stale register row; edit the register):
check_fuel_forms: SELFTEST OK (25 plants with the declared label — 6 on the table (incl. the ABSORBING-cone plant), 3 on the hypothesis register, 15 compiled decoys: the C4 four (type True / wrong worker / contradictory hypothesis caught by the register / extra binder), the whole-project audit's two decoys verbatim (review_bad _zero about runNDFuel; review_shift at literal 0), wrong fuel position, swapped worker-side and wrapper-side arguments, changed measure, wrapper calling another worker, hidden premise, and three _zero decoys (a POSITIVE control ABSORBING, a term for a binder, fuel 1) — each rejected with its own message; and the F-1 stale-carrier plant P24 (a stale-valid .olean over a source that no longer compiles: the gate FAILS naming the module); unplanted table green)
check_fuel_forms: forms partition OK (62 MEASURED + 13 ABSORBING + 0 ambient-reachable + 6 ambient-unreachable = 81 fuel'd workers)
check_fuel_forms: OK (81 fuel'd workers: 62 MEASURED (obligation of the contract's shape incl. argument correspondence against the wrapper's body; every obligation + proof cone ⊆ the standard three; 12 of them under a hypothesis, each = a reviewed row of fuel_hypotheses.txt, both directions), 13 ABSORBING = kill at zero (the _zero lemma is the worker at literal 0 on its own binders = the monad's absorbing element, cone ⊆ the standard three; propagation NOT proved — lem TODO 13), 0 reachable-AMBIENT = the 0 rows of fuel_forms_pending.txt exactly, 6 ambient unreachable from the drive cone)
check_failure_reach: instrument built + census taken in 7 s (FAILURE_REACH rows 21276, FAILURE_RANGE rows 11331; counts: {"generated:monadic_ascribed":263,"generated:pure_or_unresolved":1255,"handwritten:pure_or_unresolved":126})
check_failure_reach: SELFTEST OK (5 plants with the declared message — a new site in a generated exec-closure definition, a DISCARDABLE dead let-binding, an unsealed class edit, a phantom row, an edited tally — and the unplanted register green)
check_failure_reach: instrument built + census taken in 6 s (FAILURE_REACH rows 21276, FAILURE_RANGE rows 11331; counts: {"generated:monadic_ascribed":263,"generated:pure_or_unresolved":1255,"handwritten:pure_or_unresolved":126})
check_failure_reach: OK (239 pure failure sites = the 239 register rows exactly (237 in the exec dependency closure + 2 unresolved-owner; key = file/owner/token/message, both directions); position classes unchanged; 0 DISCARDABLE; reach UNREACHABLE-BY-INVARIANT=170 REACHABLE=48 UNKNOWN=21; every row sealed; tally line consistent)
check_lem_sync: OK (src 20c5b3a382ed464ba28ee42d40950af3d11f454050cb80eaaf280f00bc20b1f7, gen 77527ca73a3c79a836a7027062cc38aa1252c1e1c553d0a5c8d60a1d6ef8aa38)
check_lem_sync: lean OK (src 20c5b3a382ed464ba28ee42d40950af3d11f454050cb80eaaf280f00bc20b1f7, gen f4893e95ac3462defae87f737580b172f4e4e1cf35941d5be07edd82c8df808e)
check_fork_drift: SELFTEST OK (14 plants with declared verdict/message: S1-S10 prerequisite/locale/name controls; S11 copied-content control; S12 inside-listed-file drift; S13/S14 duplicate/missing content pins; unplanted gate green)
check_fork_content: OK — 84 source files content/mode-pinned
check_fork_drift: OK — layer 1: 84 oracle-surface files = manifest (set, C-locale canonical, no duplicates); layer 2: 29 differing generated files, all hash-pinned (merge-base b9aeedcb4dd438763b0eef7f95ac19e93875d7de; lem-pin 38f87d5 = lem -v)
check_fixture_freeze: OK (16 fixture files match the pinned manifest; name set exact)
```

From `cerberus-roots-nonc-locale`:

```text
check_lakefile_roots: SELFTEST — planting on a scratch copy of lakefile.toml (loud plant banner; nothing in the tree is touched)
comm: file 1 is not in sorted order
comm: file 2 is not in sorted order
comm: input is not in sorted order
comm: file 1 is not in sorted order
comm: file 2 is not in sorted order
comm: input is not in sorted order
  PLANT OK   [dropped root Core_aux_auxiliary] -> check_lakefile_roots: FAIL — generated module(s) NOT a Lake root (their obligations would never build):
  PLANT OK   [phantom root Phantom_auxiliary] -> check_lakefile_roots: FAIL — Lake root(s) with no generated module:
  PLANT OK   [unrooted generated Orphan_auxiliary] -> check_lakefile_roots: FAIL — generated module(s) NOT a Lake root (their obligations would never build):
  check_lakefile_roots: OK (218 roots = 218 generated modules + the exe root Main; 85 auxiliary modules listed as roots — names only; every carrier is built by check_fuel_forms.sh)
check_lakefile_roots: SELFTEST OK (3 plants red, baseline green)
```

### Independent contract probes

Corrected `readiness_sorry.lem` (review input, not a project change):

```text
open import Pervasives
val hole : nat -> nat
declare lean target_rep function hole = `sorry`
let observed : nat = hole 0
```

Generation succeeded and emitted the `sorry` definition quoted above.
This disproves the unconditional generator claim; it does not demonstrate
a `sorry` in the gated Cerberus execution surface.

Corrected `readiness_seed.lem`:

```text
open import Pervasives
val cfg : unit -> nat
declare lean target_rep function cfg u = 0
declare {lean} reader val cfg
val read_cfg : unit -> nat
let read_cfg u = cfg ()
val enter : nat -> (unit -> nat) -> nat
let enter seed thunk = thunk ()
declare {lean} reader_seed val enter
val captured : unit -> nat
let captured u = enter 99 (fun _ -> read_cfg ())
```

The generated module plus `#eval captured 7 ()` and
`example : captured 7 () = 7 := rfl` compiled successfully. The result is
7, not the supplied inner seed 99: the closure already carries its reader.
The README demo plus `#eval double 21` and
`example : double 21 = 42 := rfl` also compiled and printed 42. A shipped
`examples/ppcmem-model/bitwiseCompatibility.lem` was independently generated
and its Lean output compiled successfully against the freshly built LemLib.

Derived from the completed Lem logs: 101 negative probes, ten invariance
cases, and 36 parity cases. The parity cases comprise 32 ordinary successful
comparisons/expected-both-fail checks and four registered XFAILs
(`p_str_bytes`, `p_str_escapes`, `f_int_of_big_num`, `f_int32_overflow`).
The printed generation tally was 56 passed, zero failed, zero skipped.
These inventories are not a general semantic-equivalence proof.
