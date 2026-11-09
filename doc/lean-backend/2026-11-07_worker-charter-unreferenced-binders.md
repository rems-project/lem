# Worker charter: the backend's emission warnings (TODO item 54): unreferenced binders and inert `termination_by`

Date 2026-11-07. Orchestrator [AGENT]. Branch `fix/unreferenced-binders`, worktree
`worktrees/lem-lean-fix/unreferenced-binders` (created with `scripts/new-worktree.sh lem-lean fix/unreferenced-binders`),
base = mainline `mdd/lean-backend` `b154377` (the current cerberus pin is `e6d8db5`; the two commits since are docs-only).
Lean 4.35.0 on both repositories. This is the lem-lean HALF of the item: the backend and LemLib change, the suite at zero
warnings, the record and the re-pin recipe. The cerberus half (the pin dance, regeneration, the Lean-only generated delta
across the tree, the gates and the battery) is a separate slice the orchestrator charters after the three cerberus slices
now in flight have landed, because it rewrites the generated files those slices touch. Touch nothing outside this
repository; never read-write the cerberus checkouts (read-only measurement of their sources is allowed, below).

## Provenance

- TODO item 54 ([AGENT 2026-10-19], price S; re-measured at the Lean 4.35 move, `2026-10-21_lean-4.35-record.md` §7) and
  the cerberus `lean_frontend/TODO.md` generated-tree warnings entry (2026-10-19). [USER 2026-11-07] the go-ahead for the
  item as a fourth parallel slice, on the operator's `lake check` of the cerberus landing reporting the linter noise; the
  working-practices rule (the operator's global and the container doc): warnings get fixed, never suppressed or left
  standing, and a suppression option (`set_option linter.* false`, `@[nolint]`) hides a problem rather than fixing it.
- Measured on the cerberus primary checkout at mainline `1e5f2cbca` (2026-11-07, derived from Lake's stored build logs
  under `lean_frontend/.lake/build`, the modules still in the tree only): 825 warnings in the generated tree, of two kinds
  and no other — 676 `Variable name … is not explicitly referenced` (the `linter.unusedVariables` family) in 44 generated
  modules (the largest: `Cmm_csem` 128, `Defacto_memory` 92, `Core_typing` 53, `Core_reduction` 48, `GenTyping` 45) and
  147 ``unused `termination_by`, function is not recursive`` in 29 generated modules (`Cmm_csem` 16, `Errors` 14,
  `Mem_common` 14, `Cn` 10); two more in the hand-written `CerbMem.lean` (fixed by the cerberus half-mirrors slice, not
  yours). LemLib's own build carries four of the first kind (`lean-lib/LemLib/List_extra.lean:39,47`, `Word.lean:197`,
  `Machine_word.lean:40`: `x :: xs` arms using one of the two, `BitSeq len s bl` using two of three, `size_itself`'s
  `x`). The comprehensive suite's `lean-compile` emitted 175 (87 + 88) at the 4.35 move.

## The defects (in `src/lean_backend.ml` at the base; Lean output only)

1. **Inert `termination_by`.** The derived-comparison and size emitters append `termination_by structural cmpx_` /
   `sizex_` unconditionally: the list/option/sum comparison helpers (`:10028-10065`), `beq_derived` and
   `compare_derived` (`:10111`, `:10131`), the list/option/sum size helpers (`:10248-10259`). Lean 4.32+ warns when the
   definition does not recurse (a type with no recursive constructor argument: cerberus `Driver.lean:186` and `:194`,
   `step_kind.beq_derived`/`compare_derived`). The `lemSize` type emitter already guards the clause with
   `recursive_here` (`:10270-10281`): the model to follow. The `declare {lean} structural val` path (`:5900-5914`) is
   user-designated and documented "never inert"; leave it.
2. **Unreferenced binders bound by name.** Pattern variables and parameters are rendered under their source names
   (`name_var_output` `:4275`; the binder rendering `binder_of` `:6340-6352`; `fun_pattern` `:8170`, `:8283-8293`; the
   match-arm and `function`-arm paths; lambda, `let` and `let rec` parameters) whether or not the body references them.
   Lean warns on each (cerberus `Driver.lean:579,592,614`: `err` in arms that return a constant). The typed AST already
   has the facilities a decision needs: `C.exp_to_free` (`:4763`), `exp_bound_names` (`:2078-2084`),
   `Pattern_syntax.pat_vars_src`.

## M1: the backend fix and LemLib (Lean output only; the OCaml output byte-identical)

- Item 1: emit the clause iff the definition actually recurses (for a mutual block: iff the block does; Lean's rule is
  per definition — measure which the 4.35 elaborator wants on a mutual block where only some members recurse, and
  pin the answer in a probe). The derived comparisons recurse exactly through constructor fields of the block's own
  types; the option and sum helpers never recurse (their clause is always inert); the list helpers always do.
- Item 2: bind a pattern variable or parameter the body never references with a leading underscore ON THE SOURCE NAME
  (`_err`, not `_`): the name stays greppable against the Lem and the OCaml, and Lean's linter accepts the prefix as
  the declared intent. A binder that IS referenced is never renamed. Decide by the typed AST's free variables of the
  scope (never by text), and cover every binding form the backend renders: match and `function` arms, tuple and record
  patterns, `let` patterns, lambda parameters, the parameters of `def`/`let rec`/mutual members, the equation-compiler
  clauses, instance methods, the derived-instance and size emitters' own binders (`x1`/`y1` in a constant arm). Where
  the backend already emits a positional wildcard (`_x%d`, `:6350`) keep it. Beware: a binder referenced only from a
  nested scope the backend renders separately (a hoisted `let`, a `lemLetRhs_…` helper, a measure obligation shell in
  `*_auxiliary.lean`, the fuel wrapper/worker pair, a reader instance) counts as referenced; the fuel-forms tool in
  cerberus unfolds wrapper bodies and compares the worker call argument by argument by POSITION, so a renamed binder is
  harmless there, but say so in the record after checking `test/Unit/FuelFormsTool.lean` (read-only).
- A binder that is a `declare {lean} structural val`'s designated parameter, a measure parameter, a reader or fuel
  binder, or any name another emitted text refers to (the `termination_by structural <param>` clause, the `_zero`
  lemma statements, the obligation shells, `lemHyp` binders) must keep its name even if the body does not reference it;
  enumerate these cases in the record with the cite for each.
- LemLib: fix the four hand-written sites by the same rule (`_xs`, `_len`, `_x`), no semantics change; the
  `LemLibTheorems` statements are unaffected (confirm by building).
- Gate: the comprehensive suite's `lean-test` package and `lean-lib` build with `-DwarningAsError=true` (one
  `moreLeanArgs` line each), so `lean-compile` and the LemLib build FAIL on any warning from now on; a warning that
  cannot be removed for a project-level reason is suppressed at the one declaration with a stated reason and listed in
  `doc/lean-backend/README.md` (expected: none). [AGENT 2026-11-07]: a build flag is the cheapest structural check for
  this class; the operator may strike it.
- The OCaml backend is untouched: `make lean-invariance` (the suite's OCaml-output invariance lane) and a byte-compare of
  the cerberus generated OCaml are the proof (the latter in the cerberus half; here, the suite).

## M2: the tests and the measurement

- Comprehensive suite probes (`tests/comprehensive/test_*.lem` + the `lean-test` checks): a non-recursive type's derived
  comparison and size (no clause), a recursive one (clause present), a mutual block with one recursive member, and an
  unreferenced variable in each binding form above; the text-fidelity/layout checks updated for the new shapes; a
  negative plant (a suite file that would warn) proving `-DwarningAsError` bites.
- `cd tests/comprehensive && make lean` green at zero warnings; `lean-lib` build green at zero warnings; the root `make`
  for `./lem`. Quote last lines verbatim; derived counts labelled.
- The cerberus measurement, read-only and generation-only (no cerberus compile here: the box carries three other
  workers): run the new `./lem` with the cerberus Makefile's exact `lean-prelude-src` flags (`make -n lean-prelude-src`
  in `/home/dev/projects/cerberus-lean-proj/cerberus-lean`, read-only) over its `frontend/model/*.lem` into a scratch
  directory under this worktree's `.tmp/`, and diff the text against `cerberus-lean/lean_frontend/generated/` at
  `1e5f2cbca`: report the number of `termination_by` clauses removed, binders underscored, and that nothing else moved
  (every other hunk is a finding); also regenerate the OCaml (`make -n prelude-src`) into scratch and confirm it is
  byte-identical to `ocaml_frontend/generated/`. This is the expected delta the cerberus re-pin slice will verify.

## M3: documentation and the re-pin recipe

- TODO item 54 DONE (never renumbered; the row states what landed and the date); `DESIGN.md` and the manual chapter
  where the derived-instance and binder emission rules are described; the record
  `doc/lean-backend/2026-11-07_unreferenced-binders-record.md` (the mechanism, the measured counts before/after, the
  kept-name cases, the gate, the cerberus expected delta); the RECORDS.md index row; a consumer note
  `doc/lean-backend/2026-11-07_consumer-note-cerberus-unreferenced-binders.md` with the re-pin recipe (the container
  doc's: `git -C deps/lem-pinned reset --hard <commit>`, `opam upgrade --switch=. --no-depexts lem` from
  `cerberus-lean/`, the Lake rev and the three lake-manifests, `scripts/fork_drift_manifest.txt`'s `lem-pin` prefix,
  `make prelude-src lean-prelude-src`, the expected Lean-only delta, OCaml byte-identical, the hand-written measure
  proofs and the fuel-forms gate to re-run, the stale `.lake` artefacts of removed modules to delete).

## Gates and process

- You run the lem-lean gates yourself (the suite, the LemLib build, the invariance lane); the orchestrator re-runs
  them at the boundary. Every lake/lean invocation through `/home/dev/projects/cerberus-lean-proj/cerberus-lean/scripts/capped`
  with `CERB_MEM_MAX=32G` (the suite's `CAPPED=` variable); every make/opam command through
  `/home/dev/projects/cerberus-lean-proj/scripts/ce` (the opam switch, the git redirects). Exit 137 is a failure.
- Three other workers share the box: before any build or sweep check `cat /proc/loadavg` and wait for the 1-minute load
  below 12; one heavy job at a time from you. Runs longer than a few minutes go through the harness's background
  execution, never a poller, waiter, sleep loop or gate script. Never `pgrep -f`/`pkill`. No network. `/tmp` is
  unreadable: scratch under this worktree's `.tmp/`, deleted at slice end. Shell is zsh (`${=var}`, quoted globs, never
  pipe a build through `head`).
- Commits: one coherent commit per milestone on green gates, the message stating what was verified, provenance tags on
  every decision, ending with `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`. Never quote the operator's
  words. Never commit on `mdd/lean-backend` or `master`; nothing pushed. The cerberus pin does not move in this slice.
- A blocker the charter does not resolve is a committed park record
  (`doc/lean-backend/2026-11-07_unreferenced-binders-park.md`) and a stop. The grind tripwire: a single build or sweep
  approaching an hour is a stop-and-report.
- Report format at the end: commit hashes with one line each, `git diff --stat b154377..HEAD`, every gate's last lines
  verbatim, the before/after warning counts (derived, labelled), the kept-name cases, the cerberus expected delta, and
  what could not be done.
