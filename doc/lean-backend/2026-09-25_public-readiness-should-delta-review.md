# Public-readiness SHOULD block — independent delta review (lem-lean)

[AGENT — independent delta review, third pass, Claude Fable subagent,
2026-09-25]

**Range reviewed:** `6b20bfd..67ec5de` on `cleanup/public-readiness-should-20260925`
(base = the landed MUST head; [USER 2026-09-25] approved the merge as
planned, per the coordinator; mainline `mdd/lean-backend` = `6b20bfd`).

```
$ git log --oneline 6b20bfd..67ec5de
67ec5de S1-S5/S7-S8/M9: reconcile public contract and record verified follow-up
fd048db S8/S11-S13/version: preserve build identity and fail closed in native probes
003c188 M8: restore AVL linking notice and ship license with installed LemLib
$ git merge-base --is-ancestor 6b20bfd 67ec5de && echo yes   → yes
```

**Method and limits.** Read-only `git show`/`diff`/`grep`, `python3` text
comparison, from the audit worktree; read-only `git show`/`grep` of
cerberus-lean objects (branch `cleanup/public-readiness-should-20260925` @
`57ed81ca7`) for pin/consequence cross-checks. No build, no `make`/`lake`/
`opam`/`lem`. Every gate line quoted from the remediator's record
(`doc/lean-backend/2026-09-25_public-readiness-followup.md`) is a CLAIM
pending the orchestrator's independent gate. No network: the OCaml 3.12.0
LICENSE URL cited by the record could not be fetched. Tallies computed here
are *derived*. Judgements are [AGENT]. Grades: P1 blocks merge; P2 fix before
merge; P3 fix after; N note.

## Findings, most severe first

No P1. No P2.

| # | Grade | Where (at 67ec5de) | Finding | One-line fix |
|---|---|---|---|---|
| T1 | P3 | `lean-lib/LemLib.lean:259-263` | The only runtime change in the range is `@[never_extract]` on the public `fuelExhausted` wrapper — correct and minimal — but the doc comment directly above it is unchanged and still says "Unfolds to the opaque core — same cone hygiene", i.e. the very reasoning S13 disproved (closed-term extraction keys on the *head constant* of `fuelExhausted 0`, so a protected core does not protect the wrapper's closed application). Every other `never_extract` in the file carries an adjacent rationale (`:207-220` failwithI pair, `:224-235` fuelExhaustedWith pair); this one's rationale lives only in `lean-lib/README.md:39-43` and the record. | Add a 4-line comment beside the attribute: mechanism, `p_lem_size` strict-native regression, record link. |
| T2 | P3 | `doc/lean-backend/2026-09-25_public-readiness-followup.md` (S13 row `:27`, `:95-97`) | The lem-lean record does not state the consumer consequence of a runtime change (`grep -i 'consumer\|LemLib\|pin'` finds no re-pin sentence). The correct statement — "LemLib itself changes the native extraction attribute; unchanged generated model text does not mean the runtime dependency was unchanged" — is in the *cerberus* follow-up record (`lean_frontend/docs/2026-09-25_public-readiness-followup.md:147-148`), and the cerberus SHOULD branch did re-pin (`lakefile.toml:70 rev = "67ec5de7…"`, `fork_drift_manifest.txt:416 lem-pin=67ec5de7…`). No cerberus-sl consumer note was found in either range (expected cerberus-side). | Append one line to lem-lean's record: LemLib runtime changed at `fd048db`; every Lake consumer must re-pin; a cerberus-sl re-pin note is owed from cerberus-lean. |
| T3 | P3 | `lean-lib/NOTICE.md:17-26` (was `:17-22` at 6b20bfd) | The sentence "Maintainers should resolve that inherited exception-reference ambiguity before making more specific downstream licensing assurances" was removed. The *reference* ambiguity is genuinely resolved by restoring the referenced text, and the replacement hedges correctly ("source-notice restoration, not a new licensing grant or a legal conclusion about a particular downstream distribution"); but the M8 ledger asked for the Lean-port classification to be "resolved by the maintainer", and no `[USER]`/maintainer ruling is recorded for closing that call. | Append one line: maintainer confirmation of the Lean-translation classification remains open (or record the operator's acceptance with `[USER]` provenance). |
| T4 | N | `LICENSE:84-102` | The +20 lines reproduce the OCaml special exception ("As a special exception to the GNU Library General Public License, you may link, statically or dynamically, …"). [AGENT, from memory, not measured] this matches the OCaml 3.x LICENSE wording; byte-for-byte comparison is UNVERIFIED-OFFLINE (no network; no OCaml LICENSE in the local switches — the only hits were other packages' files). `c99e3f59:LICENSE` (Lem's svn import) and `master:LICENSE` do not contain it, so in-repo history cannot be the donor; the record correctly cites the OCaml URL. | Operator: `diff` against the URL when networked. |
| T5 | N | `doc/lean-backend/TODO.md` | Rows 10/11/14/17 moved to a new "Closed items — historical rulings retained" table byte-identically (python row compare: identical); rows 3/6/7/22 reworded (none contained a `[USER` quote at either end). Rows 15 and 19, also marked RESOLVED/DELIVERED, remain in the open table — the split is inconsistent. | Move 15 and 19 to the closed table verbatim. |
| T6 | N | `scripts/test_version.sh:6`, `tests/comprehensive/parity/test_failure_admission.sh:5`; `doc/manual/backend_lean.md:239-249` | Both new scripts use `mktemp -d "${TMPDIR:-/tmp}/…"`; on a host where `/tmp` is unwritable (this sandbox) `make lean` now fails loudly at its first target unless `TMPDIR` is set — fail-closed, but the Quickstart does not mention `TMPDIR`. The manual's `make lean` description names the version test but not the admission plant. | One sentence in the README on `TMPDIR`; add "XFAIL-admission plant" to the manual's list. |
| T7 | N | `scripts/capped:2-4`, `:34-35` | The Cerberus preamble sentence "Apart from the exceptions listed below…" is now paraphrased ("This script is covered by Cerberus's BSD 2-clause license below…") while `:4` still says "Original license notice follows". BSD-2 copyright line, conditions and disclaimer are intact. | Say "adapted notice follows". |
| T8 | N | `opam:22-25` | `license: ["BSD-3-Clause" "BSD-2-Clause" "LGPL-2.0-only" "LGPL-2.1-or-later"]` is accurate as base licences (pset/pmap headers name the Library GPL v2 without "or later"; the wrapper is BSD-2). SPDX can express the exception as `LGPL-2.0-only WITH OCaml-LGPL-linking-exception` once T3 is settled. | Optional, after T3. |
| T9 | N | `doc/lean-backend/2026-09-25_branch-worktree-inventory.md:3-14`, `:18-20` | Advisory (`[AGENT] Classification is advisory. No branch, tag or worktree is deleted.`), counts labelled derived, hashes verbatim; the snapshot predates the MUST landing (shows `mdd/lean-backend = 38f87d5…`, the SHOULD branch at `6b20bfd`, 7 worktrees vs 8 now) and says so ("may differ from the overseer's later landing"). Branch count 14 matches the current `git for-each-ref` (derived). | None. |
| T10 | N | `src/lean_backend.ml:1310-1316` | The import heuristic's allowlist means a *user* Lean module literally named `Nat`/`List`/`String`/… now needs `declare {lean} extra_import`; DESIGN `:539-545` says so. | None. |

First-pass **F2** (cerberus fork-drift string-equality on `lem -v`) is
CLOSED on the cerberus SHOULD branch: `scripts/check_fork_drift.sh:169-175`
accepts "a 7–40 hex prefix, bare or in a hash-bearing tag-distance-gHASH
form", strips `-dirty`, and rejects a non-hex `LEMRELEASE` fallback
(read-only observation; that branch is gated separately).

## (1) LemLib `never_extract` — the runtime change

```
$ git diff 6b20bfd 67ec5de -- lean-lib/LemLib.lean
-def fuelExhausted {α : Type} (witness : α) : α :=
+@[never_extract] def fuelExhausted {α : Type} (witness : α) : α :=
   fuelExhaustedWith "lem: fuel exhausted" witness
```
Exactly the attribute on the public wrapper; no other `lean-lib/*.lean`
change; `lean-lib/lean-toolchain` unchanged (`leanprover/lean4:v4.28.0`).
Behaviour beyond extraction timing: none — `never_extract` is a compiler
attribute; the definition, its unfolding, and every `f_lemFuel_zero … := rfl`
lemma are untouched. Runtime: a closed sentinel application is now evaluated
where its branch is reached, not hoisted into module initialisation.

Rationale in-file: **absent** (T1). Rationale in `lean-lib/README.md:39-43`
(verbatim): "The `fuelExhausted` wrapper, like its opaque primitive, is
marked `never_extract`: this keeps a closed sentinel in its branch instead
of allowing native extraction to evaluate it during module initialization.
The `p_lem_size` parity probe exercises the sufficient-fuel path with
`LEAN_ABORT_ON_PANIC=1`; general fuel propagation still requires proofs."

Record evidence (claim, verbatim from the follow-up record `:81-89`):
```
=== p_lem_size ===
  FAIL: PARITY DIFF (< OCaml reference, > Lean; lean exit 134):
1,4c1
< psum leaf: 7
…
> Aborted (core dumped)
```
and after the fix (`:149-150`): `  OK: parity (4 lines byte-identical to the
OCaml reference; pin matches)`.

[AGENT — reasoning from the Lean 4 runtime, not measured here] Why the
MUST-era gates did not see it although the non-failure parity leg merged
stderr into the compared output: compiled Lean `main` disables panic
messages during module initialisation and re-enables them afterwards, so a
closed-term-extracted `fuelExhausted 0` evaluated at init panicked
*silently* and returned its witness — output unaffected, parity green —
whereas `LEAN_ABORT_ON_PANIC=1` still aborts at init. The record's diagnosis
("a real premature native sentinel evaluation, not an insufficient-fuel
observation") is consistent with this; the probe's `results` list is itself
a closed top-level term, which is why no line printed before the abort.
The strict `LEAN_ABORT_ON_PANIC=1` leg (`run.sh:155`) is what makes this
fail-open class visible; the same probe is the regression.

Sweep (derived, heuristic): every other LemLib def whose body is an
unconditional panic (`rationalFrom*`, `realFrom*`, `unsupported*`,
`natLnot`) already carries `never_extract`; the `| 0, … => fuelExhaustedWith
…` arms are inside multi-arm workers, not closed wrapper applications.

Consequence: stated correctly in the *cerberus* record and acted on there
(re-pin to `67ec5de7…` in `lakefile.toml` and `fork_drift_manifest.txt`);
absent from the lem-lean record (T2).

## (2) `src/lean_backend.ml` +24 — the qualified-core-name import heuristic

Rule (`collect_cr_simple_import`, `:1298-1320`): for a function `CR_simple`
rep (via `Backend_common.on_cr_simple_applied`, fired only for the current
file's expressions) or — new — a `TYR_simple` type rep (`:6917`, replacing
an inline copy that excluded only `LemUnsupported.`), take the text before
the first `.`; if it starts uppercase, is **not** in the fixed
`prelude_namespaces` list (`Nat Int Bool String Char List Option Array
ByteArray Except Sum Prod Unit PUnit Empty PEmpty Ordering Fin Float
UInt8…USize Int8…ISize LemUnsupported`), and is not already collected, emit
`import <Head>`. The exclusion is therefore **only** for those 30 names,
not for everything. `LemUnsupported.` is a backend-intercepted marker
protocol (`lean_unsupported_check_cref :2483-2492` refuses any use), never a
module — excluding it is correct and was already the type path's behaviour.
Risk of dropping a needed import: only a user module literally named like a
prelude namespace (T10); DESIGN `:539-545` documents the escape
(`extra_import`) and calls it "a syntactic import heuristic … not general
Lean name resolution"; the in-code comment says the same.

Fixture (`test_target_reps.lem:421-428`): `core_successor = `Nat.succ``
applied (`core_successor 41`) and bare/higher-order (`core_successor_bare :
nat -> nat = core_successor`), each with a `{lean}` assert = 42 ✓. The
record's `PASS: core_successor_applied_ok` / `core_successor_bare_ok`
lines are claims.

## (3) Version identity

`Makefile:5` (verbatim): `LEMVERSION:=$(shell git describe --long --dirty
--always 2>/dev/null || echo $(LEMRELEASE))` — `--long` forces
`<tag>-<N>-g<hash>` even at N = 0; untagged stays the bare abbreviated hash.
`scripts/test_version.sh` (36 lines): `mktemp` scratch repo, `GIT_CONFIG_
GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1`, unsets `GIT_DIR`/`GIT_WORK_TREE`;
tags exist only in the scratch repo; runs the production recipe via `make
-f "$root/Makefile" version` and asserts five cases: untagged `= <short>`,
exact annotated tag `= release-test-0-g<short>`, dirty tag `…-dirty`
(dirtied through a tracked file; `src/version.ml` is gitignored so the
recipe's own output cannot dirty it), post-tag `release-test-1-g<short>`,
archive fallback `= 2026-05-01` with `.git` renamed and `GIT_DIR` pointed at
a missing directory. The fallback is **labelled, not fail-closed at lem**
(upstream behaviour retained): `:32-33` "A source archive has no commit
identity. Keep the release fallback, and let consumers that require a hash
reject it rather than inventing one"; README `:124-127` says the same. The
consumer does reject it (cerberus SHOULD comparator requires hex). Wired as
`lean-version`, first prerequisite of `make lean`.

## (4) M8 — notices and licence

LICENSE `:84-102`: preamble "reproduced below from OCaml 3.12.0 LICENSE
(checked 2026-09-25) … This restores the source notice for the files and
translations named above; it does not assign the src/ulib license to them
or grant a new exception." followed by the exception paragraph (T4 on
verification). `opam`: `homepage`/`bug-reports`/`dev-repo` → `OathTech/
lem-lean` ✓; licence list (T8) ✓; description names the fork ✓. Install:
`Makefile:31 cp LICENSE "$(INSTALL_DIR)/share/lem/LICENSE"` beside the
existing `cp -R lean-lib` (which carries `NOTICE.md`); the record's two
`cmp` results are claims. NOTICE scope statements checked against the
tree: translations retain LGPL terms ✓, exception text reproduced ✓, `src/
ulib` unchanged ✓, base-licence list matches `opam` ✓, wrapper BSD-2 ✓,
install ships LICENSE ✓. No relicensing or new grant is asserted anywhere;
the maintainer-resolution sentence was dropped (T3). `scripts/capped`
header edit (T7) leaves the BSD-2 notice intact.

## (5) Parity runner: S12/S13

`run.sh` diff: `OCAMLLIB` (an environment variable ocamlfind honours;
assigning to an already-exported variable keeps it exported, hence the
record's `Unbound module Stdlib`) renamed to `LEM_OCAML_RUNTIME` ✓. XFAIL
admission: `parity_mismatch` is reset per probe (`:103`) and set to 1 only
at (a) a failure probe whose Lean binary exits 0 where OCaml fails
(`:148`), (b) a failure probe whose stdout prefixes differ (`:152`), (c) a
non-failure probe with a PARITY DIFF **and** Lean exit 0 (`:160`); the
driver (`:172-177`) admits XFAIL only when `xreason` is set **and**
`parity_mismatch = 1`, otherwise prints `FAIL: registered probe did not
reach its expected parity disagreement (not XFAIL)` and sets `status=1`.
OCaml build failure (`:119-120`), vacuous Lean exe (`:145`), OCaml not
failing on a failure probe, and a PARITY DIFF with a nonzero Lean exit
(the `Aborted` case) all stay RED ✓. The non-failure Lean leg now runs
under `LEAN_ABORT_ON_PANIC=1` (`:155`) — strict native. The four registered
XFAILs still admit: `p_str_*` via (c), `f_int*` via (a).
`test_failure_admission.sh` plants a PATH-shadowing `ocamlfind` that exits
2, runs `run.sh f_int32_overflow`, and requires nonzero exit + the planted
message + `not XFAIL` + no `XFAIL (expected` — a plant by construction,
`set -euo pipefail`, wired as `lean-parity-admission`. Panic control:
`tests/comprehensive/Makefile:257` leg 1 is `env -u LEAN_ABORT_ON_PANIC
./…` — unset for that leg only; leg 2 (`:273`) still sets it ✓.

## (6) Docs

DESIGN `:522-523` declare table now has `ground_rep` and `extra_import`
rows ✓; `:447-452` state claim qualified ("`Backend_common.on_cr_simple_
applied` is a separate process-global callback … `process_file.ml`
supplies `St.current_module_name` … remains TODO 6") ✓; import heuristic
paragraph ✓. README `:85-93`: "Direct invocations default to 64G; the
comprehensive/parity harness defaults to 16G. `CERB_MEM_MAX=none` is an
explicit, loudly reported uncapped opt-out. `CERB_JOB_CGROUP=/delegated/
path` requests a caller-owned cgroup subtree; setup failure in that mode
is fatal." ✓ (matches `capped:117-121`, `:156-159`, `:187-190`); "##
Validation levels" `:104-127`: newcomer smoke / backend regression /
consumer-release, "Neither fork currently has a GitHub Actions Lean
certification workflow" ✓, version behaviour ✓. TODO (T5). Manual: `make
lean` description rewritten, "not a proof about every possible Lem input"
✓, stale "registered follow-up" for backend-derived sizes fixed ✓, runtime
build now via `../scripts/capped` ✓. Dated records touched in range: only
`2026-09-25_branch-worktree-inventory.md` and
`2026-09-25_public-readiness-followup.md` (both new) ✓. The follow-up
record opens with the verbatim `[USER 2026-09-25]` quote ✓ and `[AGENT]
Prepared by OpenAI Codex under operator direction` ✓; it also corrects its
own commit message's count ("36 parity successes and 4 registered
differences" → 32 + 4 = 36) without a history rewrite ✓; derived 107
negatives = 105 + 2 ✓.

## (7) Policy

New targets: `lean-version` and `lean-parity-admission`, both first in the
`lean` prerequisite list, both `set -euo pipefail` with hard assertions;
the admission test is itself a plant. No other gate added. `2>/dev/null`
in changed scripts at 67ec5de: `Makefile:5` (the version fallback, by
design), `tests/comprehensive/Makefile:309` and `parity/run.sh:168`
(optional expected-failure list probes, pre-existing), the wrapper's nine
inherited cgroup probes — none on a build step ✓. Provenance ✓ (above).

## (8) Merge readiness

`6b20bfd` is an ancestor of `67ec5de` ✓. Pin-moving set (derived from
`git diff --stat`): `src/lean_backend.ml` (+24), `lean-lib/LemLib.lean`
(runtime attribute), `Makefile` (version recipe, LICENSE install),
`scripts/capped` (comment), `scripts/test_version.sh` (new), `tests/
comprehensive/Makefile`, `parity/run.sh`, `parity/test_failure_admission.sh`
(new), `test_target_reps.lem` (+9), `opam`, `LICENSE`, `lean-lib/NOTICE.md`.
The cerberus SHOULD branch (`57ed81ca7`) already pins `67ec5de7…` in
`lakefile.toml` and the fork-drift manifest (read-only observation).

## VERDICT

[AGENT] **Merge-ready as is at 67ec5de**, conditional on the orchestrator's
independent green gate. The three P3s are record/comment items (T1 in-file
rationale beside the load-bearing attribute; T2 the consumer-consequence
line in lem-lean's own record; T3 the maintainer-open line in NOTICE) —
append-only fixes that do not touch code or tests. The runtime change is
exactly the one attribute and is the right fix for a real silent
init-time panic; the import heuristic is a bounded allowlist documented as
a heuristic; the version recipe and XFAIL admission are tested and
fail-closed in the right direction; notices are restored without any new
grant; no dated record before 2026-09-25 was edited. Merge authority rests
with the operator.
