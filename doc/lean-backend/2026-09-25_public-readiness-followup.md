# Public-readiness follow-up — 2026-09-25

[USER 2026-09-25]: asked for the rest (the SHOULD work, M8/M9, and hash-bearing version output at exact release tags) to be picked up on new branches starting at the final heads, with the overseer agent handling the landing.

[AGENT] Prepared by OpenAI Codex under operator direction; independent overseer review and landing are separate. Work starts from Lem `6b20bfd02de924d078725efa96c6675115b8b17a`
and Cerberus `c13a1054133b49c954fe27ac4c1b4e33a418c51f`, each on
`cleanup/public-readiness-should-20260925` in a new worktree. Mainlines,
existing worktrees, shared switches and dependency checkouts are not modified.
No landing, publication, tag, deletion or upstream message is performed.
Scratch version tests create tags only inside disposable test repositories.
The overseer owns landing; the earlier MUST records remain unchanged.

## Dispositions

| Item | Remediation | Evidence / remaining boundary |
|---|---|---|
| M8 | Restore the OCaml 3.12.0 linking exception referenced by the copied AVL source headers; align base-license metadata; install LICENSE beside the runtime; clarify the cap notice's scope. | Original donor LICENSE and headers linked in NOTICE.md; original Lem import `c99e3f59b5b7963c00f827e3634985dcdf23e43b`. This is source-notice restoration, not a new license or legal opinion. |
| M9 | Separate public web observations from anonymous Git and clean dependency-download checks. | External publication checks remain open below; a proxy error is not evidence that a repository is private. |
| S1 | Reconcile current TODO/manual text; closed rows are separated while original rulings remain verbatim. | `ground_rep` already had ground/polymorphic smoke coverage; its dedicated negative guard probe remains open. OCaml `genlist` performance remains open; Lean sorting was already closed. Historical `refined-cerberus` requests stay historical. |
| S2 | Fork package homepage/dev-repo/bug-report links now agree with the fork README. | Actual external issue creation needs the signed-in operator check below. |
| S3/S8 | Explain smoke, comprehensive/non-Lean regression and consumer release levels; document cap defaults, delegation, explicit opt-out, and the absence of fork Lean CI certification. | Manual evidence, not inherited upstream badges or the existence of a Make target, establishes the checked scope. |
| S5 | Document `ground_rep`, `extra_import` and the callback/current-module exceptions to state centralization. | Checked against `lean_backend.ml`, parser and backend-common call sites. |
| S7 | Refresh branch/worktree classifications without deletion. | [Snapshot](2026-09-25_branch-worktree-inventory.md); derived counts and operator-only deletion candidates. |
| S11 | Qualified prelude namespace references no longer infer a nonexistent module import (`Nat.succ`); use the same rule for simple type representations. | Applied and bare references compile and evaluate in `test_target_reps.lem`. The heuristic is not general Lean name resolution; explicit imports/raw expressions remain necessary for other namespace/module mismatches. |
| Version | `git describe --long` preserves the hash at an exact annotated tag. | Production Makefile recipe exercised in an isolated Git repo: untagged, tag, dirty tag, post-tag, archive fallback. Archives cannot attest a hash they do not contain. |
| S12 (added here) | Preserve an exported `OCAMLLIB` in the parity runner; scope the panic test's non-aborting control explicitly. | The copied toolchain exposed the old private-variable collision as `Unbound module Stdlib`; the gate is rerun with a real exported OCAMLLIB and panic-abort setting. |
| S13 (added here) | Mark the public `fuelExhausted` wrapper `never_extract`; require native parity probes to abort on reached panics; reject infrastructure failures as XFAIL. | Strict native `p_lem_size` exposed premature sentinel extraction. Its sufficient-fuel outputs must match with abort enabled. A planted OCaml compiler failure on a registered XFAIL probe must remain red. |

## M9 — public state and external exits

Read-only anonymous web observations on 2026-09-25:
[OathTech/lem-lean](https://github.com/OathTech/lem-lean) and
[OathTech/cerberus-lean](https://github.com/OathTech/cerberus-lean) are public
pages, identify their upstream forks, and land on `mdd/lean-backend` and
`mdd/cerberus-lean`, respectively. This is page access, not proof of Git
transport, published cleanup commits, tags, Lake fetches or a fresh install.

The two anonymous issue pages display “Issue creation is restricted in this
repository”. An operator must check issue creation while signed in as an
external user / repository administrator; this observation alone does not
establish which GitHub setting or authentication rule caused the banner.
The question was sent to the operator; no issue or setting was changed here.

Anonymous Git probes disable global/system Git configuration, credential
helpers and terminal prompts. Exact invocations and verbatim failures:

```text
GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_COUNT=0 GIT_CONFIG_PARAMETERS= GIT_TERMINAL_PROMPT=0 git -c credential.helper= ls-remote --symref https://github.com/OathTech/lem-lean.git HEAD refs/heads/mdd/lean-backend
fatal: unable to access 'https://github.com/OathTech/lem-lean.git/': CONNECT tunnel failed, response 403

GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_COUNT=0 GIT_CONFIG_PARAMETERS= GIT_TERMINAL_PROMPT=0 git -c credential.helper= ls-remote --symref https://github.com/OathTech/cerberus-lean.git HEAD refs/heads/mdd/cerberus-lean
fatal: unable to access 'https://github.com/OathTech/cerberus-lean.git/': Failed to connect to 127.0.0.1 port 41039 after 0 ms: Couldn't connect to server
```

Both return 128 (bounded at 40 seconds). **UNVERIFIED-OFFLINE** applies to
anonymous Git/fresh dependency downloads, not to the successful web-page
observations. No proxy setting or machine-global configuration was changed.
The post-publication commands below remain operator work.


## Findings exposed by the isolated run

The initial runs are retained in local logs; none is counted as passing.
They exposed three distinct problems before the final run:

From `lem-gates.log` (rc 2):

```text
  FAIL (leg 1): nonzero exit 134 without LEAN_ABORT_ON_PANIC
```

From `lem-gates-final.log` (rc 2):

```text
Error: Unbound module Stdlib
```

From `lem-gates-verified.log` (rc 2):

```text
=== p_lem_size ===
  FAIL: PARITY DIFF (< OCaml reference, > Lean; lean exit 134):
1,4c1
< psum leaf: 7
< psum empty node: 0
< psum tree: 11
< psum chain 300: 1
---
> Aborted (core dumped)
```

The first control had inherited the caller's panic-abort setting and now
unsets it explicitly. The second came from the runner overwriting an already
exported OCAMLLIB with Lem's own runtime path; it now uses LEM_OCAML_RUNTIME.
The third was a real premature native sentinel evaluation, not an
insufficient-fuel observation. The wrapper now shares its primitive's
never_extract protection; the same strict native probe is the regression.
Expected failure admission now begins only at an actual parity disagreement,
so a build/setup error or changed OCaml reference pin cannot satisfy XFAIL.

The environment copies preinstalled OCaml dependencies into an owned switch;
its OPAMROOT, OCAMLFIND_CONF and OCAMLLIB point into that owned copy. A cold
source build was run, followed by comprehensive generation/Lean compilation,
negative probes, invariance, strict native parity and the non-Lean goldens.
Copied dependencies do not constitute a fresh anonymous dependency download.


## Measured implementation and gate result

Implementation pin: `fd048dbaeed9e0031496aa6ae4a56bb20c07841a`; M8 packaging/notice commit:
`003c188f0f57870eff1aa6f7f90caac2b2dd43fa`. The following documentation
commit changes no implementation or tests. The source build and all required
Lem gates pass. Final combined run: rc 0, 505.47 seconds
(excluding the initial wait for the shared heavy-job slot).

**Derived tallies:** 56 generated test modules, 107 negative refusals,
10 invariance fixtures, **36 parity probes total: 32 successes and four
registered XFAILs**. The non-Lean gate has 893 artifact rows and 216 exit
rows across nine emitters. No baseline was changed.

**Record correction:** the body of commit `fd048dbaeed9e0031496aa6ae4a56bb20c07841a`
says “36 parity successes and 4 registered differences”. That is a counting
error: 36 is the total, including the four differences. The derived counts
above come from `lem-final.log`; no history rewrite was performed.

Exact final command (owned environment adaptations are explicit):

```bash
set -euo pipefail; c=../cerberus-lean-cleanup-public-readiness-should-20260925; c=$(cd "$c" && pwd); export OPAMROOT="$c/.tmp/readiness/opam-root" OCAMLFIND_CONF="$c/_opam/lib/findlib.conf" OCAMLLIB="$c/_opam/lib/ocaml" CERB_MEM_MAX=32G CAPPED="$c/scripts/capped" LEAN_ABORT_ON_PANIC=1 TMPDIR="$PWD/.tmp/readiness/tmp"; opam exec --switch="$c" -- "$CAPPED" make -C tests/comprehensive lean; opam exec --switch="$c" -- "$CAPPED" make nonlean-regress; opam exec --switch="$c" -- make INSTALL_DIR="$PWD/.tmp/readiness/install" install; cmp LICENSE .tmp/readiness/install/share/lem/LICENSE; cmp lean-lib/NOTICE.md .tmp/readiness/install/share/lem/lean-lib/NOTICE.md; opam lint opam
```

Verbatim selected output:

```text
test_version: OK (untagged, exact annotated tag, dirty tag, post-tag, archive fallback)
test_failure_admission: OK (registered probe with compiler failure is red, not XFAIL)
=== Generation: 56 passed, 0 failed, 0 skipped ===
info: Test_target_reps_auxiliary.lean:153:0: PASS: core_successor_applied_ok
info: Test_target_reps_auxiliary.lean:157:0: PASS: core_successor_bare_ok
  OK: 11 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
  OK: 260 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
/home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-cleanup-public-readiness-should-20260925/opam: Passed.
```

The p_lem_size strict native regression tail, verbatim:

```text
=== p_lem_size ===
  OK: parity (4 lines byte-identical to the OCaml reference; pin matches)
```

LICENSE and NOTICE copies were byte-compared after installation (both rc 0).
The custom INSTALL_DIR stages the compiler/runtime sources; OCaml package
installation follows ocamlfind's destination, which was separately verified
to be the owned Cerberus validation switch, not the shared switch. The local
raw log is `.tmp/readiness/lem-final.log`, sha256 `c299852f08d56df3997cb85dc6d1e137df7d397d29e1299cef3b93f8fa8ef8a1`.
It is not a tracked evidence archive. The commands and selected output here
are the committed evidence.

## Exact post-publication checks (operator)

Run from a new directory outside existing checkouts, after the overseer has
published the selected heads. These commands deliberately ignore global
rewrites and credentials; a public transport failure is a failure, not a skip.

```bash
set -eu
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_COUNT=0
export GIT_TERMINAL_PROMPT=0
unset GIT_CONFIG_PARAMETERS GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE
mkdir public-readiness-check
cd public-readiness-check
export GIT_CEILING_DIRECTORIES="$PWD"
timeout 60s git -c credential.helper= ls-remote --symref https://github.com/OathTech/lem-lean.git HEAD refs/heads/mdd/lean-backend
timeout 60s git -c credential.helper= ls-remote --symref https://github.com/OathTech/cerberus-lean.git HEAD refs/heads/mdd/cerberus-lean
timeout 180s git -c credential.helper= clone --branch mdd/lean-backend https://github.com/OathTech/lem-lean.git
timeout 180s git -c credential.helper= clone --branch mdd/cerberus-lean https://github.com/OathTech/cerberus-lean.git
git -C lem-lean merge-base --is-ancestor fd048dbaeed9e0031496aa6ae4a56bb20c07841a HEAD
lem_pin=$(sed -n 's/^rev = "\([0-9a-f]*\)"/\1/p' cerberus-lean/lean_frontend/lakefile.toml)
git -C lem-lean cat-file -e "$lem_pin^{commit}"
git -C lem-lean checkout --detach "$lem_pin"
```

Then execute both README recipes in their new public clones, retaining full
logs and using fresh project switches/dependency downloads. Do not substitute
local mirrors or the already-built workspace and call that M9 closure.
After actual tag publication, run `git ls-remote --tags` for both the annotated
ref and its peeled `^{}` ref, fetch/checkout each tag and rebuild. `lem -v`
and the OCaml `cerberus --version` must carry the checked-out commit prefix;
the in-repo version tests establish the generator behavior, not published-tag
availability. No tag was created in either project repository here.

## Sweep addendum (2026-09-25, orchestrator [AGENT])

Consumer consequence of S13 (review T2): `lean-lib/LemLib.lean` itself changed — the `never_extract` attribute on the
public `fuelExhausted` wrapper — so the LemLib RUNTIME every consumer links changed even though no generated model text
did (cerberus-lean's regenerated OCaml and Lean trees are byte-identical to the previous pin's under this lem). Every
consumer must move its Lake `LemLib` rev to this lem-lean head or later; cerberus-lean did so at its five pin sites.
Landed on `mdd/lean-backend` at `67ec5de` on the [USER 2026-09-25] approval of the whole merge and sweep as
proposed; this sweep adds the in-file rationale (T1), the NOTICE line (T3) and brings the independent delta reviews
(`2026-09-24_public-readiness-must-delta-review.md`, `2026-09-25_public-readiness-should-delta-review.md`) onto the mainline.
