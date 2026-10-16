# Public-readiness remediation — MUST checkpoint

Date: 2026-09-24. [AGENT] Cleanup of the
[public-readiness review](2026-09-24_public-readiness-review.md).
Base: review `07b709e95b604aff305c3a3dc6b5ebeed088796b`, carrying Lem mainline
`38f87d5fa6b29ec90edfa457faba8a309e32c118`. Branch:
`cleanup/public-readiness-20260924`. Implementation pin: `1235498fa300c79504684a3bf774b902bc3b7458`.
Gates below measured the implementation bytes committed at that pin;
the then-built binary carried the review-branch dirty version label.

## Scope and changes

| Ledger | Remediation | Evidence / remaining boundary |
|---|---|---|
| M1 | Repository-local `scripts/capped`; comprehensive and parity defaults resolve it from the repository. No ancestor environment discovery. | Shell syntax and full comprehensive suite; cap fallback behavior is documented. Cap platform requirements were reclassified SHOULD by the operator. |
| M3 | Explicit fork clone/local opam installation; generate LemLib, generate a client, compile it and check/evaluate `double 21 = 42`. | Local recipe execution below; anonymous public refs and fresh dependency downloads remain M9. |
| M4 | Refuse bare `sorry` function and type target representations, including unused declarations and parameterized function reps. Existing positive hole fixtures now use concrete reps with value assertions; four new negative cases cover the refusal. | Arbitrary embedded Lean text remains trusted input. This is not a parser/soundness check for every Lean snippet. Cerberus replaces three excluded CMM reps with named unsupported markers. |
| M4 follow-up | `lean-generate` now returns failure for failed single-file and joint generation. | During remediation, a rejected positive fixture printed FAIL but the phase returned success; stale generated files could have concealed it. A failing-generator plant returns nonzero. |
| M5 | Correct failure/byte/numeric/correspondence claims in backend, manual and runtime pages. | Four registered parity XFAILs remain; unused pure failures can be erased; abort-on-panic controls reached native panics; default recursion is partial; general propagation/completion monotonicity is not proved. |
| M8 | Restore both OCaml source notices in LemLib; describe translations accurately; identify runtime and cap-wrapper license exceptions in LICENSE and NOTICE. | The source headers refer to a linking exception whose scope is ambiguous in the inherited LICENSE. Notices are preserved; maintainer resolution is still needed before more specific licensing assurances. No new exception or relicensing is invented. |
| M11 | Document lexical seed extent and positional-order hazards, including same-typed argument slides; correct the manual's obsolete one-reader restriction. | Existing three-reader value tests exercise injection; no claim of dynamic re-seeding of prebuilt closures. |

The original review and dated design records are unchanged. The top-level
README changes stay within its fork note and license clarification.

## Ledger refinements (original review preserved)

[AGENT] These amendments implement the operator's 2026-09-24 engagement
rules; they do not rewrite the dated review.

| ID / grade | Repository and location | One-line action | Effort / checkpoint state |
|---|---|---|---|
| M1a / MUST | Both; comprehensive Makefile/parity runner, common.sh, capped | Remove private absolute defaults and required/implicit container environment. | M; implementation above, gated below |
| M1b / SHOULD | Both backend/frontend READMEs | Describe cgroup/systemd prerequisites and the intentional loud fallback precisely. | S; documented with M1 |
| S9 / SHOULD | Cerberus `scripts/check_exec_totality.sh:37`, ENFORCE default | Make enforcement the default; retain any report mode only as an explicit, labelled choice and plant-test it. | S; next block |
| S10 / SHOULD | Cerberus `scripts/check_fork_drift.sh:108`, resolve_upstream_tree/help | Remove the machine-absolute fallback and private-mirror recipe; document public upstream setup or explicit CERB_UPSTREAM_TREE. | S; next block |
| S11 / SHOULD (new measurement) | Lem `src/lean_backend.ml:1298`, collect_cr_simple_import | Add a focused qualified-core-name import case and avoid emitting nonexistent `import Nat` for `Nat.succ`. | S; registered from the M4 fixture failure, not fixed here |

## Measurement environment and commands

The worktree starts without generated/build trees. Local measurement uses
the preinstalled OCaml 5.4.0 toolchain and dependencies. The command wrapper
waits for foreign release/Lake/Dune builds and runs one job at a time;
Lean commands are also enclosed by Cerberus `scripts/capped` with
`CERB_MEM_MAX=32G`. The Lem suite exercises its new local wrapper inside
that outer cap. Nothing is installed into the shared switch.

```bash
opam exec --switch=/path/to/preinstalled-switch -- make
opam exec --switch=/path/to/preinstalled-switch -- make lean-libs
# Under the outer Cerberus cap:
opam exec --switch=/path/to/preinstalled-switch -- make -C tests/comprehensive lean
opam exec --switch=/path/to/preinstalled-switch -- make nonlean-regress
(cd lean-lib && ../scripts/capped lake build)
# Client commands are exactly the generation/Lake block in README.md.
```

Required gates: **exit 0**. Exact local invocation (2026-09-24):

```bash
export CERB_PROJ="$PWD" CERB_MEM_MAX=32G GIT_CONFIG_GLOBAL=/dev/null; opam exec --switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean -- /home/dev/projects/cerberus-lean-proj/cerberus-lean/scripts/capped bash -c "make lean-libs && make -C tests/comprehensive lean && make nonlean-regress"
```

Derived tallies from the log: 56 generation cases; 105 negative cases;
10 invariance probes; 36 parity probes with four registered XFAILs.
The non-Lean runner reports 893 artifact rows, 216 exit rows and nine
emitters, byte-identical to its golden. Pauses for foreign work mean the
560.18-second wall interval is not a performance result.
Raw local log SHA256: `4a060225f431cd35adde216a79f4c137d8511e6cb7bd4e49a90e157d3985c8e8`.
Verbatim gate tail:

```text
=== No sorry/admit/axiom/native_decide in fuel_measure proofs modules (gate) ===
  OK: 11 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
=== No fuel numerals in LemLib or generated code (gate) ===
  OK: 260 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make: Leaving directory '/home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-cleanup-public-readiness-20260924/tests/comprehensive'
tests/nonlean-regress/run.sh
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
```

The standalone runtime completed successfully (39 jobs). The README's
client block was then executed in a new directory: **exit 0**, verbatim tail:

```text
✔ [33/35] Built Demo (148ms)
ℹ [34/35] Built Check (148ms)
info: Check.lean:3:0: 42
Build completed successfully (35 jobs).
```

The first client attempt exposed a missing `lean_lib Demo` declaration
in the draft recipe. It was corrected and the complete client block rerun
from a new directory before publication of these instructions. Existing
runtime unused-variable warnings remain. The compiled theorem reports
use only the standard Lean axioms listed in the runtime README.

The generation-failure plant was:

```bash
make -C tests/comprehensive lean-generate LEM=/bin/false TESTS=test_types_basic.lem
```

It returned **exit 2** (expected refusal). The restored Pset and Pmap
header blocks, through their modification credits, each compare verbatim
to the corresponding OCaml source notice. `git diff --check` passed.


Two intermediate failures were retained during development: the old
positive fixture was correctly refused, then its replacement used a
`Nat.succ` target that caused the existing import heuristic to request a
nonexistent `Nat` module. The fixture now uses a concrete local helper.
[AGENT] The qualified-core-name import case is a follow-up portability
limitation, not evidence that arbitrary Lean target text is validated.

## Publication and remaining work

M9 is **UNVERIFIED-OFFLINE**. After operator-authorized publication, run
with redirects disabled in a new directory:

```bash
GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 GIT_TERMINAL_PROMPT=0 \
  timeout 30s git ls-remote --symref https://github.com/OathTech/lem-lean.git \
  HEAD refs/heads/mdd/lean-backend
GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 GIT_TERMINAL_PROMPT=0 \
  timeout 180s git clone --branch mdd/lean-backend \
  https://github.com/OathTech/lem-lean.git public-lem-check
timeout 10s git -C public-lem-check cat-file -e 1235498fa300c79504684a3bf774b902bc3b7458^{commit}
```

This verifies the implementation pin; the exact final consumer revision
is recorded and checked in Cerberus’s companion remediation record.
Then follow the README with a new local opam switch and empty Lake build
state. This cleanup does not tag, push, merge, change default branches,
rewrite history or delete branches/worktrees. The SHOULD block remains
for a separate checkpoint, including tracker/declare-table/CI/triage
clarifications, roots locale handling, fail-closed totality default and
fork-drift prerequisite portability. The current early announcement should
name the supported profile and experimental status, not imply a stable
release. No tag is created by this remediation.

## Closure addendum — corrections and operator provenance (2026-09-24)

[AGENT] Closure findings F3/F4, checked at Lem `9bb6c6b` and Cerberus
`0a6d59eed`. The M4 row above says "three excluded CMM reps". That is an
incorrect tally: **23** target representations were replaced by
`LemUnsupported.Cmm.*` markers in Cerberus `abe505d3d` (derived from the
`frontend/concurrency/cmm_csem.lem` diff against `e9f9d049f`). The original
body is retained as the record of the first checkpoint.

The operator's M1 split, paraphrased:

[USER 2026-09-24]: M1 is split. The absolute container defaults and the hard GIT_CONFIG_GLOBAL requirement are MUST; the cap wrapper's uncapped fallback is loud and by design, so documenting the cap prerequisites is SHOULD, not MUST.

The operator's remediation engagement rules, paraphrased:

[USER 2026-09-24]: only current-facing pages are edited; dated records and quoted rulings are never edited (superseded for the quotes by the [USER 2026-10-16] ruling that the operator's words are never quoted verbatim: the quoted rulings in dated records were paraphrased on 2026-10-16). All lem-lean non-doc changes land before a single cerberus re-pin at the end. Work stops and reports at the end of the MUST block with verbatim gate tails; merges are ff-only on the operator's per-merge sign-off after a delta review of the range.

[AGENT] The subsequently relayed orchestrator note (Cerberus `aab00b9b6`,
`lean_frontend/docs/2026-09-24_public-readiness-must-checkpoint-orchestrator-note.md`
§6) authorizes the closure slice, including these appended corrections and
one further Cerberus re-pin after the Lem closure. It does not authorize a
merge or shared-switch update. The [closure record](2026-09-24_public-readiness-closure.md)
records that slice's exact implementation pin and measurements separately.
