# Public-readiness MUST closure — Lem backend

2026-09-24. [AGENT] Closure of the independently reviewed MUST checkpoint,
per Cerberus orchestrator note `aab00b9b6`, §6. Prior reviewed head:
`9bb6c6b583c2eb4ecf6ca5b21a274dacc29e0fa4`. Implementation measured below:
`292db8b0e2a905031c797f08ebbe692a535c66c4` on `cleanup/public-readiness-20260924`.
The final documentation commit containing this record has identical backend
and test sources; Cerberus's closure record records its exact consumer pin.

## Changes and boundaries

- **F1 / M4:** the `Typ_backend` arms in `pat_typ` and `indreln_typ` now
  refuse a trimmed identifier equal to `sorry`, using the existing diagnostic.
  Two negative fixtures exercise substituted type representations in a
  constructor field and an inductive relation, respectively. Parenthesized
  target types select `TYR_subst`, bypassing the existing `TYR_simple` guard.
  Arbitrary embedded Lean snippets remain trusted input; no general Lean
  syntax validator is claimed.
- **F5 / M4:** `process_val` again has a recursive definition and a target
  representation, now backed by concrete recursive helper `process_val_body`.
  The existing `unit_match` assertion checks the same unit/tuple-match result.
  The generated auxiliary contains, verbatim, `/- removed theorem process_val_def_lemma -/`.
  This confirms the recursive rep transformation route; it does not claim
  that the removed theorem is proved.
- **F3/F4:** the [first remediation record](2026-09-24_public-readiness-remediation.md)
  has an appended correction from three to 23 CMM markers and verbatim tagged
  operator rulings. Its original body and the original review remain intact.

## Commands and evidence

Measurement date: 2026-09-24, OCaml 5.4.0, LemLib Lean 4.28.0. Existing
local build state was reused. The preinstalled OCaml switch was read for
compiler/dependencies only; no package was installed there. All Lean jobs
ran under Cerberus `scripts/capped`, `CERB_MEM_MAX=32G`, with the Lem suite's
repository-local wrapper inside it. Scratch TMPDIR and logs belong to this
cleanup worktree. A bounded runner waited for foreign release/Lake/Dune
jobs; one heavy job ran at a time. This is not a fresh public-network build.

Exact command (from the Lem cleanup root):

```bash
export CERB_PROJ="$PWD" CERB_MEM_MAX=32G GIT_CONFIG_GLOBAL=/dev/null TMPDIR="$PWD/.tmp/readiness/closure-tmp"; opam exec --switch=/home/dev/projects/cerberus-lean-proj/cerberus-lean -- /home/dev/projects/cerberus-lean-proj/cerberus-lean/scripts/capped bash -c "make && make lean-libs && make -C tests/comprehensive lean && make nonlean-regress"
```

Exit **0**. Wall interval 438.45 seconds (not a performance claim).
Derived tallies: 107 negative cases,
10 non-Lean invariance cases, 36 parity probes,
4 registered parity XFAILs.
The latter remain `f_int32_overflow`, `f_int_of_big_num`, `p_str_bytes`, and
`p_str_escapes`; no baseline was changed. Raw local log:
`.tmp/readiness/closure-lem-final.log`, SHA256
`a7d4c296fbfbfec2b74be97f89af1c886d10d833e4c235423ed34667b5c40202`.

Verbatim selected gate lines:

```text
=== Generation: 56 passed, 0 failed, 0 skipped ===
Build completed successfully (173 jobs).
  OK (leg 1): panic prints the Incomplete Pattern message, then continues with default
  OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1
  OK (leg 1): two sufficient fuels agree; insufficient gives the declared sentinel; callee starts from the full ambient
  OK (leg 2): loud exhaustion at an insufficient runtime fuel fail-stops (exit 134)
  OK (rejected as declared): negative/neg_inline_relation_type_sorry.lem
  OK (rejected as declared): negative/neg_inline_type_sorry.lem
  OK: 11 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
  OK: 260 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
```

Two unsuccessful development runs preceded the passing run. The first
rejected the recursive fixture because its rep preceded its definition;
the rep was moved after the definition. The second rejected both inline
negative fixtures in the typechecker before the renderer; the fixtures
were changed to legal substituted target types so they reach the two
intended diagnostics. Both failed runs returned exit 2; neither was
counted as a gate pass. Their local logs are `closure-lem-gates.log` and
`closure-lem-gates-retry.log`.

`git diff --check` passes. No LemLib runtime source, license text or non-Lean
backend implementation changed in this closure. Non-Lean golden comparison
is the output check quoted above, not an inferred claim from diff scope.

## Handoff

[AGENT] Ready for the orchestrator's independent re-gate and second delta
review. The next Cerberus closure re-pins once to this Lem closure's final
head before regenerating both trees. This does not authorize a merge,
shared-switch update, push, tag or announcement. The SHOULD block, M8
maintainer licensing resolution and M9 public availability/fresh-clone
checks remain outside this closure. The sequencing hazard recorded in the
orchestrator note remains: old Cerberus mainline cannot regenerate with
the new `sorry` refusal until its cleanup lands.
