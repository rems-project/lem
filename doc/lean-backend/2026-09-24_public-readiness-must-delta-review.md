# Public-readiness MUST checkpoint — independent delta review

[AGENT — independent delta review, Claude Fable subagent, 2026-09-24]

**Range reviewed:** `38f87d5..9bb6c6b` on `cleanup/public-readiness-20260924`
(reviewed from branch `audit/public-readiness-must-20260924`, HEAD = the
same commit `9bb6c6b583c2eb4ecf6ca5b21a274dacc29e0fa4`).

```
$ git log --oneline 38f87d5..9bb6c6b
9bb6c6b M3 M5 M11: publish tested build path and bounded backend contract
1235498 M1 M4 M8: local cap, refuse sorry reps, restore runtime notices
07b709e docs: review public readiness of Lem Lean and Cerberus Lean
```

**What this review did:** read-only inspection of the range with `git
show`/`git diff`/`git grep`, `sha256sum`, `grep`, `wc`, `python3` text
comparison; read-only `git grep`/`git show` against the cerberus-lean
repository objects (`e9f9d049f`, branch `cleanup/public-readiness-20260924`)
for the pin-consequence section. **What it did not do:** no build, no
`make`, `lake`, `opam` or `lem` invocation (the orchestrator's marker
`.tmp/orch-ALL-DONE` was ABSENT in the cleanup worktree at review time, so
the built `./lem` was not run); nothing was modified outside this file;
nothing pushed. The remediation record's gate outputs are therefore quoted
as its CLAIMS and marked as such; this review verifies source, text and
structure, not execution. Tallies computed here are labelled *derived*.
Every judgement below is [AGENT]. Grades: P1 blocks merge; P2 fix before
merge; P3 fix after; N note.

## Findings, most severe first

No P1. No P2.

| # | Grade | Where (at 9bb6c6b) | Finding | One-line fix |
|---|---|---|---|---|
| F1 | P3 | `src/lean_backend.ml:7175-7180`, `:7226-7231` (`Typ_backend` render); `src/parser.mly:283`, `:305` | An inline backend TYPE `` `sorry` `` (e.g. `val x : `sorry``) is rendered unchecked, while the same token in EXPRESSION position (`parser.mly:485` → `Backend`) is refused at `:5830` and `:5960`, and declared type reps are refused (`TYR_simple`, `:2382-2390`). The README's "raw Lean snippets remain trusted inputs" qualification keeps the published claim true; the exp/type asymmetry is undocumented. | Add the same `String.trim (Ident.to_string i) = "sorry"` refusal at the two `Typ_backend` render sites (or document the asymmetry beside the M4 note in DESIGN). |
| F2 | P3 | cerberus-lean `scripts/check_fork_drift.sh:172-176` (outside this range); lem `Makefile:4` | The fork-drift gate compares manifest `lem-pin=` (`scripts/fork_drift_manifest.txt:393` = `38f87d5`) against the second word of `lem -v` by string equality, but lem's version is `git describe --dirty --always` — abbreviation length is object-store dependent (measured here: `9bb6c6b` vs `--abbrev=8` `9bb6c6b5`), and the string can also carry `-dirty`, a `<tag>-N-g<hash>` form once any tag exists, or the `LEMRELEASE` date (`2026-05-01`) from a tarball build. | Compare by hex prefix (≥7 chars) after stripping `-dirty`; fail loudly on a non-hex version string. |
| F3 | P3 | `doc/lean-backend/2026-09-24_public-readiness-remediation.md:17` | The M4 row says "Cerberus replaces three excluded CMM reps with named unsupported markers"; measured: cerberus mainline `e9f9d049f` `frontend/concurrency/cmm_csem.lem` has 23 `` `sorry` `` Lean target reps (derived) and the companion branch `cleanup/public-readiness-20260924` @ `0a6d59eed` has 0 `sorry` reps and 23 `LemUnsupported.Cmm.*` markers (derived). "Three" could not be reconciled with either number. | Append an erratum line to the remediation record with the measured count (do not rewrite the dated body). |
| F4 | P3 | `doc/lean-backend/2026-09-24_public-readiness-remediation.md:15`, `:28-29` | Two operator decisions are referenced without the `[USER <date>]` tag or verbatim quote: "Cap platform requirements were reclassified SHOULD by the operator" and "the operator's 2026-09-24 engagement rules". The record distinguishes them as operator-called in prose, but the house convention (rulings quoted `[USER <date>]`) is not met. | Append an addendum quoting the two rulings verbatim with `[USER 2026-09-24]` provenance. |
| F5 | P3 | `tests/comprehensive/test_target_reps.lem:204-215` (the `process_val` rep was at 38f87d5 `:309`) | One non-`sorry` positive coverage item was dropped rather than replaced: `declare lean target_rep function process_val = `sorry`` on a `let rec` was the trigger for `def_trans.ml:253` `_def_lemma` generation (recursive def with a target rep → auxiliary-file lemma with a unit-match-then-tuple-match body). The rep is gone, so that route is no longer exercised. Low risk: theorems render as comments on the Lean target (README:216-217), so the original parser-ambiguity failure cannot recur in that form. | Give `process_val` a concrete parameter-binding rep (e.g. ``declare lean target_rep function process_val v path = (0 : nat)``) if the `_def_lemma` route is meant to stay covered, or state the drop in the fixture header. |
| F6 | N | `tests/comprehensive/negative/neg_target_rep_sorry{,_applied,_parameter}.lem` | The three function fixtures are distinct at source level (unused `CR_simple`, applied `CR_simple`, `CR_inline`) but all three are caught by the declaration-level `lean_sorry_rep_check` (`:2369-2390`, run first in `lean_defs` `:8415`); the use-site arms `:5830` and `:5960` are defence in depth exercised by no fixture. An inline body expression `` `sorry` `` would exercise `:5830`. Not a defect. | Optional fifth fixture with an inline `` `sorry` `` expression in a body. |
| F7 | N | `doc/lean-backend/README.md:84-92` | The wrapper paragraph is true as written but omits: unset `CERB_MEM_MAX` → `64G` in the wrapper (`scripts/capped:117`) while the suite exports `16G` (`tests/comprehensive/Makefile:8`); the `CERB_MEM_MAX=none` loud opt-out (`capped:118-121`); and the `CERB_JOB_CGROUP` owned-runner refusal, exit 2 (`capped:156-159`, `:187-190`). | Add one sentence with the two defaults and the `none` opt-out. |
| F8 | N | `README.md:207-209`; `scripts/capped:2-35` | Root README cites "(2026-09-24 provenance check, `38f87d5`)" for `scripts/capped`, a file that does not exist at `38f87d5` (it is new in `1235498`). The wrapper header reproduces Cerberus's LICENSE preamble including "Apart from the exceptions listed below" with no exception list following. | Cite `1235498` (or `e9f9d049f`, the copied source) and drop or complete the dangling "exceptions listed below" phrase. |
| F9 | N | `src/lean_backend.ml:2369-2390` | `lean_sorry_rep_check` walks `c_env_all_consts env.c_env`, i.e. every loaded module including `-i` libraries not being generated; a `sorry` Lean rep anywhere in the loaded environment refuses every output file. Fail-closed and the error names the constant; note only. | None required. |
| F10 | N | `doc/lean-backend/README.md:38-39` | The toolchain sentence states "Cerberus uses Lean 4.32.2" (true: cerberus `lean_frontend/lean-toolchain` @ `e9f9d049f` = `leanprover/lean4:v4.32.2`) but does not say the 4.32.2 pairing was exercised by THIS cleanup's gates (which ran lem's own suite on 4.28.0). The cerberus companion's gates are where that pairing is tested. | Optional: "…uses Lean 4.32.2 (its own build gates the pairing)". |

S5 (declare table lists `ground_rep` and `extra_import`): **deferred, not
done** — `grep -n 'ground_rep\|extra_import' doc/lean-backend/DESIGN.md`
returns nothing at 9bb6c6b. This matches the remediation record's statement
that the SHOULD block ("tracker/declare-table/CI/triage clarifications")
remains for a separate checkpoint. Reported as status per the brief, not a
finding.

## R-A — Review document integrity

```
$ git show 07b709e:doc/lean-backend/2026-09-24_public-readiness-review.md | sha256sum
829b78d822878242023f4354a7f29f20031ee0fd77882f206bbc8f67f7c58641  -
$ git show 9bb6c6b:doc/lean-backend/2026-09-24_public-readiness-review.md | sha256sum
829b78d822878242023f4354a7f29f20031ee0fd77882f206bbc8f67f7c58641  -
$ git log --oneline 07b709e..9bb6c6b -- doc/lean-backend/2026-09-24_public-readiness-review.md
(no output)
```

`git show --stat 07b709e` touches only the review document (1195 lines).
[AGENT] PASS: byte-identical, never rewritten.

## R-B — M4 code, fixtures, test file, Makefile

### The `src/lean_backend.ml` hunk (1235498; 43 diff lines — derived: +33, +2, +1/−6, +1)

Four hunks, all `sorry`-related; no other backend behaviour changed:

1. `:2359-2390` new `lean_sorry_rep_error` / `lean_sorry_rep_check`.
   Function reps: `CR_simple`/`CR_inline` via `exp_backend_idents e`
   (trims every `Backend` ident; traverses `Fun`, `App`, `Case`, `Let`,
   `Typed`, `Paren`, … per `:2322-2358`), `CR_infix` via the trimmed
   `Ident`, `CR_special` via each trimmed `CR_special_rep` string. Type
   reps: `TYR_simple` in `env.t_env`. Verbatim error text:
   ```
   "Lean backend: target representation `sorry` is forbidden (%s); provide a real Lean implementation, use failwithI for a declared runtime failure, or use a LemUnsupported. marker for an unsupported operation"
   ```
   `%s` is `Path.to_string cd.const_binding` (the constant) or
   `Path.to_string path` (the type); the location is `cd.spec_l` / the
   rep's `l`. `Reporting_basic.err_general : bool -> Ast.l -> string -> exn`
   (`reporting_basic.mli:137`) — a `Fatal_error`, raised.
2. `:5828-5830` bare `Backend (sk, i)` arm: trimmed `"sorry"` → raise
   (`"backend expression"`).
3. `:5959-5960` the applied arm. REMOVED (verbatim, 38f87d5 `:5924-5930`):
   ```
                     | Backend (_, i) when Ident.to_string i = "sorry" ->
                       (* sorry is a term, not a function — drop applied arguments.
                          Annotate with the expression's type so Lean can infer it
                          in contexts like let bindings. *)
                       let typ = Typed_ast.exp_to_typ e in
                       let src_t = C.t_to_src_t typ in
                       [Output.flat [from_string "(sorry : "; pat_typ src_t; from_string ")"]]
   ```
   Replaced by `raise (lean_sorry_rep_error (exp_to_locn e) "applied backend expression")`.
   (The guard is untrimmed as before; a `` ` sorry` `` with whitespace falls
   to `List.map trans (e0 :: args)` and `trans e0` hits the trimmed arm 2 —
   consistent.)
4. `:8415` `lean_sorry_rep_check A.env;` after `St.reset_per_file ()` in
   `lean_defs` — runs per output file, before any emission.

[AGENT] Coverage as briefed: CR_simple/CR_inline/CR_infix/CR_special ✓,
type reps (`TYR_simple`; `TYR_subst` carries a Lem `src_t`, so a Lean
`sorry` can only enter through a constructor whose own rep is checked) ✓,
applied use site ✓, old drop-arguments arm gone ✓, error names constant +
escape hatches ✓. Gap: inline `Typ_backend` — F1. Library check:
`grep -rn sorry library/` hits only `lean_constants`/`isabelle_constants`
reserved-word lists and `gen_lean_constants.lean:45`; no library rep is
`sorry`, so the whole-environment walk (F9) does not fire on Pervasives.

### The four negative fixtures (each first line is the `EXPECT:` header the runner greps with `grep -qF`, `tests/comprehensive/Makefile:281-295`; the fragment match is `grep -qF` at `:289`)

| Fixture | Route (source level) | Arm that fires (code level) |
|---|---|---|
| `neg_target_rep_sorry.lem` | `val hole : nat -> nat` + `target_rep function hole = `sorry``, never used | `lean_sorry_rep_check`, `CR_simple` |
| `neg_target_rep_sorry_applied.lem` | same rep, `let observed : nat = hole 0` (the review's `(sorry : Nat)` counterexample) | `lean_sorry_rep_check`, `CR_simple` (before the `:5960` arm is reached) |
| `neg_target_rep_sorry_parameter.lem` | `target_rep function hole x = `sorry``, applied | `lean_sorry_rep_check`, `CR_inline` (`typecheck.ml:2460`) |
| `neg_target_rep_sorry_type.lem` | `type missing` + `target_rep type missing = `sorry`` | `lean_sorry_rep_check`, `TYR_simple` |

Distinct at source level ✓; three share the declaration-level arm (F6).
Rejection for the wrong reason is a FAIL in the runner
(`"  FAIL (rejected for the wrong reason)"`), so the declared reason is
load-bearing ✓.

### `tests/comprehensive/test_target_reps.lem` (−160/+… per stat; derived from the diff)

REMOVED: header "Merged from …" history comment; Section 2 `get_mode_val =
`sorry`` + `test_sorry_applied`; Section 4's seven `sorry` reps
(`make_digest`, `get_mode`, `current_mode`, `get_error_ctx`, `get_name`,
`get_count`, `transform_val`) and the vacuous `assert mode_check_compiles :
true`; Section 5's `debug_print = `sorry`` and — the one non-hole removal —
`declare lean target_rep function process_val = `sorry`` (F5); the long
explanatory comments. ADDED: concrete reps (`get_mode_val m = (42 : nat)`,
`make_digest = `rep_succ`` with a local `rep_succ`, `get_mode u = Just (7 :
nat)`, `current_mode u = ModeA`, `get_error_ctx u = (9 : nat)`, `get_name u
= "context"`, `get_count u = (3 : nat)`, `transform_val = `rep_succ``,
`debug_print u = ()`), `declare lean target_rep type digest = `Nat``
(digest is no longer opaque; `layout_state` stays opaque under
`skip_instances`), and six value assertions (`rep_applied`, `mode_check`,
`current_mode_check`, `rep_hof`, `rep_chain`, `unit_match`). Sections 6–8
unchanged. [AGENT] Net: positive coverage is stronger (value asserts
replace a `true` assert); the only coverage lost beyond the holes is F5.

### "M4 follow-up: lean-generate now returns failure" vs the Makefile hunk

Before (38f87d5): the `for` loop counted `fail` and the recipe line ended
with `echo "=== Generation: … ==="` — exit status of `echo`, i.e. 0
regardless; the two joint-generation branches printed `FAIL:` and
continued. **Fail-open confirmed.** After (9bb6c6b `:317-318`,
`:324`, `:329`): `echo …; \` / `test "$$fail" -eq 0` and `… (joint)"; exit
1;` on both joint branches. **Closed.** The runner's `lean-negative`
already ended with `exit $$fail` (`:295`). The remediation's plant
(`make -C tests/comprehensive lean-generate LEM=/bin/false
TESTS=test_types_basic.lem` → "exit 2") is a CLAIM not re-run here; the
Makefile text supports it (`make` returns 2 on a failing recipe).

## R-C — M1: the repository-local cap wrapper

```
$ git diff 38f87d5 9bb6c6b -- tests/comprehensive/Makefile   (excerpt)
-CAPPED ?= /home/dev/projects/cerberus-lean-proj/cerberus-lean/scripts/capped
+export CAPPED ?= $(abspath ../../scripts/capped)
 export CERB_MEM_MAX ?= 16G
-LAKE = $(CAPPED) lake
+LAKE = "$(CAPPED)" lake
$ git diff 38f87d5 9bb6c6b -- tests/comprehensive/parity/run.sh   (excerpt)
-CAPPED=${CAPPED:-/home/dev/projects/cerberus-lean-proj/cerberus-lean/scripts/capped}
+CAPPED=${CAPPED:-$ROOT/scripts/capped}
+if [ ! -x "$CAPPED" ]; then
+  echo "FAIL: capped Lean runner not executable: $CAPPED (set CAPPED to an executable wrapper)" >&2
+  exit 1
+fi
```

`check-capped` (`Makefile:15-16`) fails noisily if the wrapper is missing;
`export CAPPED` hands the same wrapper to the parity runner ✓.

Absolute paths: `git grep -n '/home/dev' 9bb6c6b` → 43 hits (derived), ALL
in dated records: `doc/lean-backend/2026-09-04_fuel-measure-record.md`
(2), `2026-09-05_measure-hypothesis-record.md` (2),
`2026-09-24_public-readiness-remediation.md` (2, the verbatim gate
invocation and `make: Leaving directory`), `2026-09-24_public-readiness-review.md`
(37). **Zero hits outside dated records.** `git grep -n 'env\.sh'` and
`'CERB_PROJ\|scripts/ce\b'` excluding `doc/lean-backend/2026-*` and
`doc/notes/`: **no hits.**

Wrapper vs cerberus-lean `scripts/capped` @ `e9f9d049f` (167 lines → 201):
`diff -u` shows exactly two changes — (a) a 56-line header added
(`# Repository-local copy of cerberus-lean scripts/capped at e9f9d049f.` /
`# The container environment auto-loader is deliberately omitted.` /
`# Original license notice follows; local changes use the same BSD-2-Clause terms.`
followed by the Cerberus copyright/BSD-2 text, `#`-prefixed), and (b) the
22-line "env self-load ([USER] env-trap tweak, arc-13 audit-fix batch)"
block removed — the `while [[ "$_d" != "/" ]]` ancestor walk that sourced
`scripts/env.sh`. Everything else is byte-identical. [AGENT] The difference
is deliberate and exactly what M1 demanded (no ancestor discovery). The
uncapped fallback is loud (`capped:196-199`, verbatim):
```
  echo "capped: WARNING — systemd-run NOT FOUND; running UNCAPPED" >&2
  echo "capped: WARNING — the D7 memory-cap rule is NOT enforced here" >&2
```
README `:84-92` describes cgroup-direct → systemd-run → warn-uncapped and
"If `systemd-run` exists but its user service is unavailable, the command
fails" — matches `run_reporting_kills systemd-run --user --scope …`
propagating the nonzero rc. `CERB_MEM_MAX` semantics: "upper limit, not a
minimum RAM requirement" ✓; defaults/`none`/`CERB_JOB_CGROUP` omitted (F7).

## R-D — M8 notices and licence

Byte comparison (python3, first 14 lines of each OCaml file = the boxed
header through the `(* Modified by … *)` line, against the block following
`From ocaml-lib/pset.ml:` / `From ocaml-lib/pmap.ml:` in `LemLib.lean`):
```
ocaml-lib/pset.ml: first 14 lines (header through 'Modified by' line) byte-identical to LemLib.lean block: True
ocaml-lib/pmap.ml: first 14 lines (header through 'Modified by' line) byte-identical to LemLib.lean block: True
```
LemLib.lean code: comments stripped (`--`, nested `/- -/`), blank-normalised:
```
LemLib.lean comment-stripped, blank-normalised code identical 38f87d5 vs 9bb6c6b: True
```
Other `lean-lib/` changes in range: `NOTICE.md` (new), `README.md` only.

LICENSE `:39-40` now reads: "All files except ocaml-lib/pmap.{ml,mli},
ocaml-lib/pset.{ml,mli}, src/ulib, / the Pset/Pmap translations in
lean-lib/LemLib.lean, and scripts/capped" (also fixes the upstream typo
`ocaml-libpset`). Two new paragraphs (`:79-86`) tie the translations to the
LGPL text already in the file and `scripts/capped` to its inline BSD-2
notice. No relicensing: `NOTICE.md:5` "it does not grant a new license or
claim a legal review"; `:17-23` "The original headers also refer to a
linking exception; that wording is preserved, without inventing an
additional exception for Lean or asserting that the separate LGPL 2.1
exception attached to `src/ulib` applies to these portions. Maintainers
should resolve that inherited exception-reference ambiguity…" ✓ (stated,
not resolved). `opam:24` still `license: ["BSD-3-Clause" "LGPL-2.1-or-later"]`
— NOTICE `:22-24` flags "reconcile the inherited package-level SPDX metadata"
as maintainer work ✓. The `../LICENSE` path inside the reproduced header
happens to resolve correctly from `lean-lib/`. Root `README.md:205-209`
and `lean-lib/README.md:35-37` point at NOTICE; neither claims BSD-only ✓.

## R-E — Docs (M3, M5, M11)

Checked at 9bb6c6b, each sentence against the tree:

(i) Quickstart `README.md:46-82`: fork clone `git clone --branch
mdd/lean-backend https://github.com/OathTech/lem-lean.git` (public
availability explicitly left as an operator check, `:39-41`); local switch
`opam switch create . ocaml-base-compiler.5.4.0 --no-switch --no-install`,
`opam pin add --switch=. lem . --yes`; `make`, `make lean-libs`
(`Makefile:97` exists), `make -C tests/comprehensive lean`, `make
nonlean-regress` (`Makefile:49` exists); generated demo `double`, lakefile
with `require LemLib from "../lean-lib"`, and `Check.lean` ending in
`example : double 21 = 42 := rfl` / `#eval double 21` ✓. Versions: "OCaml
5.4.0, opam 2.1.5 and Lean 4.28.0; Cerberus uses Lean 4.32.2" —
`lean-lib/lean-toolchain` = `leanprover/lean4:v4.28.0`; cerberus
`lean_frontend/lean-toolchain` @ e9f9d049f = `leanprover/lean4:v4.32.2` ✓
(F10 on the word "tested"). The `-wl` flag exists (`src/reporting.ml:347`).
The demo's exit-0 run and `info: Check.lean:3:0: 42` are remediation
CLAIMS, not re-run here.

(ii) Limitations (`README.md:205-226`): four parity XFAILs named
(`p_str_bytes`, `p_str_escapes`, `f_int_of_big_num`, `f_int32_overflow` —
matches `tests/comprehensive/parity/expected_failures.txt` exactly, four
entries) ✓; byte vs Unicode strings ✓; "Failure tests compare reached
failures under `LEAN_ABORT_ON_PANIC=1`; unused pure failures can be
erased" ✓; "not a general OCaml–Lean correspondence theorem" ✓; "theorem/
lemma statements are emitted as comments … assertions become build-time
evaluation checks" ✓ (`def_trans.ml:245` `comment_def`); "optionally
under a stated hypothesis" (fuel hypotheses) ✓; "Default recursion remains
`partial`" ✓; monotonicity/propagation "not proved by the backend (TODO
item 13)" — `TODO.md:49` item 13 is "Fuel monotonicity — two routes…" ✓.

(iii) Seeding (`README.md:223-226`; `DESIGN.md:295-304`, `:306-309`; manual `:213-219`):
lexical extent ("cannot re-seed a closure built outside that extent"),
positional order in globally sorted reader order, same-typed slide hazard
("same-typed swaps need value tests") ✓. The manual's corrected guard
sentence "at least one reader … at least N parameters … each seed
parameter must be a simple variable" matches the code:
`lean_backend.ml:4519` `if n = 0 then raise …`, `:4522` `if List.length
pats < n then raise …` (at-least, not exactly), and the `P_var |
P_var_annot` match; probes `neg_seed_noreader`, `neg_seed_arity`,
`neg_seed_nonvar` exist ✓. `TestReaderMultiCheck.lean`/`Exec.lean` exist;
`spin_fuel_irrelevant` is at `lean-test/TestFuelParamCheck.lean:87` ✓;
`LemLibPmapLaws` referenced in `lean-lib/lakefile.lean` ✓.

(iv) S5: deferred (see above).

(v) `grep -n -i sorry` over `README.md`, `doc/lean-backend/{README,
DESIGN,TODO}.md`, `doc/manual/backend_lean.md`, `lean-lib/README.md`,
`lean-lib/LemLib.lean`: every surviving mention is either the qualified
"Bare `sorry` target representations are refused … Raw Lean snippets …
remain trusted inputs" form, the pre-existing token-gate sentences, or
`LemLib.lean:74` history. At 38f87d5 the unqualified forms were
`doc/lean-backend/README.md:62-63` ("never emits `sorry`"), manual `:5`,
`:36`, `:238` — all gone. `src/lean_backend.ml:84` "sorry-emission paths
are gone (fail-closed, arc-8 S2)" is now true.

(vi) `git diff --name-only 38f87d5 9bb6c6b -- 'doc/lean-backend/2026-*'
'doc/notes/'` → only `2026-09-24_public-readiness-remediation.md` (new)
and `2026-09-24_public-readiness-review.md` (07b709e). No historical
record edited ✓. TODO item 2 removed from the table with a cited
"Discharged 2026-09-24" line (`TODO.md:9-11`) — per the register's own
rule ✓.

## R-F — Pin consequence and the version string

LemLib code unchanged ⇒ consumer-generated Lean is unaffected except at
`sorry` reps, which now refuse. `lem` (the tool) changed ⇒ cerberus-lean
must re-pin (`scripts/fork_drift_manifest.txt:393 lem-pin=38f87d5`).

**Hard sequencing fact (derived, read-only cerberus greps):** cerberus
mainline `e9f9d049f` passes `frontend/concurrency/cmm_csem.lem` to `lem
-lean` (`Makefile:165 LEM_CONC = cmm_csem.lem cmm_op.lem linux.lem`;
`:201 LEM_SRC_LEAN = $(filter-out frontend/model/core_unstruct.lem,$(LEM_SRC))`)
and that file carries **23** `declare lean target_rep function … = `sorry``
lines. Because `lean_sorry_rep_check` walks the whole environment, a re-pin
of mainline cerberus to 9bb6c6b refuses generation at the first output
file. The companion branch `cleanup/public-readiness-20260924` @ `0a6d59eed`
has 0 such reps and 23 distinct `LemUnsupported.Cmm.<name>` markers, so the
pin dance is coordinated — but the two must land together (lem first,
re-pin, re-gate, then cerberus), and the remediation record's "three" is
wrong or unexplained (F3).

Version string: `Makefile:1-4` (verbatim):
```
# Attempt to ask git for a version (tag or hash) but fall back on LEMRELEASE.
# Note that opam builds from a tar ball so LEMRELEASE will be used in that case.
LEMRELEASE:=2026-05-01
LEMVERSION:=$(shell git describe --dirty --always 2>/dev/null || echo $(LEMRELEASE))
```
`Makefile:277-279` writes `src/version.ml` (`let v="$(LEMVERSION)"`);
`src/main.ml:333` prints `"Lem " ^ Version.v`. `git describe --always`
without a reachable tag prints the abbreviated hash at `core.abbrev`
(unset here → auto-scaled to the object store):
```
$ git describe --always 9bb6c6b
9bb6c6b
$ git describe --always --abbrev=8 9bb6c6b
9bb6c6b5
$ git config --get core.abbrev  → (unset → auto);  git count-objects -v: count 1714, in-pack 10272;  git tag | wc -l → 0
```
An opam-pinned build compiles from opam's own source copy (a different
object store or none), hence `Lem 9bb6c6b5` there vs `Lem 9bb6c6b`
in-tree; `--dirty` appends `-dirty`; a tarball gives `Lem 2026-05-01`; the
first tag anyone pushes changes the format to `<tag>-N-g<hash>`. cerberus
`check_fork_drift.sh:172-176` (verbatim):
```
        live_lem=$("$LEM_CMD" -v | awk '{print $2}') || fail "'$LEM_CMD -v' failed"
        [[ -n "$live_lem" ]] || fail "'$LEM_CMD -v' printed no version"
        if [[ $REFRESH -eq 0 && "$live_lem" != "$pinned_lem" ]]; then
            fail "lem-pin stale: manifest records lem-pin=$pinned_lem, '$LEM_CMD -v' says $live_lem — …"
```
[AGENT] Fragile in the false-stale direction (fail-closed, never silently
green) — P3 with the prefix fix (F2). Plant `S9` (`:405-406`, `Lem deadbee`)
would still catch a truly wrong pin under a prefix compare.

## R-G — Policy

- New gates: none. The `sorry` refusal is a generation-time refusal that
  discharges TODO item 2; the `lean-generate` exit fix closes a fail-open
  bug in an existing phase; `check-capped`/the `run.sh -x` test are
  presence checks for the wrapper the suite already required.
- New theorems: none in the tree (the `example : double 21 = 42 := rfl` is
  README text; `LemLib.lean` code unchanged).
- `2>/dev/null`: `tests/comprehensive/Makefile` 1→1 (`:303`, optional
  `expected_failures.txt` probe — skip-list absence makes the suite
  stricter, not looser), `parity/run.sh` 1→1 (`:166`, same file), and
  `scripts/capped` 9 uses inherited verbatim from cerberus (cgroup setup
  probes with explicit `|| return 1` / `|| true` fallbacks, never a build
  step). None on an install/build step ✓.
- Dated records: untouched ✓ (R-E vi).
- Provenance: the remediation record is headed `[AGENT]`; the two operator
  rulings it leans on are not tagged/quoted (F4).

## R-H — Merge readiness

```
$ git merge-base --is-ancestor 38f87d5 9bb6c6b && echo yes
yes
```
Non-doc files in the range (the exact pin-moving set for the operator):

| File | Effect |
|---|---|
| `src/lean_backend.ml` | **changes the `lem` binary** (the only tool change) |
| `tests/comprehensive/Makefile` | suite: local wrapper default, fail-closed generation exit |
| `tests/comprehensive/parity/run.sh` | suite: local wrapper default + `-x` check |
| `tests/comprehensive/test_target_reps.lem` | fixture: holes → concrete reps + asserts |
| `tests/comprehensive/negative/neg_target_rep_sorry.lem`, `…_applied.lem`, `…_parameter.lem`, `…_type.lem` | new negative fixtures |
| `scripts/capped` | new, repository-local cap wrapper (BSD-2, from cerberus e9f9d049f) |
| `lean-lib/LemLib.lean` | comments only (verified: code identical) |
| `lean-lib/NOTICE.md` | new notice file |
| `LICENSE` | exception list + two paragraphs |

Docs: `README.md`, `doc/lean-backend/{README,DESIGN,TODO}.md`,
`doc/manual/backend_lean.md`, `lean-lib/README.md`, and the two
2026-09-24 records.

Remediation-record tallies cross-checked as file counts (derived):
`test_*.lem` 56 ✓ ("56 generation cases"); `negative/neg_*.lem` 105 ✓;
`parity/probes/*.lem` 36 ✓; `invariance/*.lem` 10 ✓; proofs modules 7
(`lean-test/*_lemMeasureProofs.lean`) + 4 (`parity/probes/*.proofs.lean`,
the scan set of `check_no_sorry_proofs.sh:19`) = 11 ✓ ("11 proofs modules
scanned"). The quoted gate tail, the demo run, the failing-generator plant
and the raw-log SHA256 remain the remediator's CLAIMS pending the
orchestrator's independent gate.

## VERDICT

[AGENT] **Merge-ready as is**, conditional on the orchestrator's
independent green gate on 9bb6c6b (this review ran nothing). R-A through
R-H pass: the review document is byte-identical; the M4 refusal covers
every declared rep form and the applied use site with the old
`(sorry : T)` arm removed and no other behaviour touched; the fail-open
`lean-generate` exit is closed; the cap wrapper is repository-local with
the ancestor `env.sh` walk deliberately removed and no container path left
outside dated records; the OCaml notices are reproduced byte-for-byte,
LemLib's code is unchanged, and the licence ambiguity is left to the
maintainer; every changed doc sentence checked is true at 9bb6c6b and no
unqualified "never emits sorry" survives; no dated record was edited. The
five P3s (inline `Typ_backend` `sorry` asymmetry; prefix-compare in the
cerberus fork-drift gate; the "three vs 23" count and the untagged
operator rulings in the remediation record — both as appended errata, not
rewrites; the dropped `_def_lemma` fixture route) are fix-after items.
Operationally the re-pin is a hard two-repo step: mainline cerberus at
e9f9d049f cannot generate against this lem until its companion
(`0a6d59eed`, 23 markers) lands with it. Merge authority rests with the
operator.

## Closure delta — second pass at 6b20bfd

[AGENT — independent delta review, second pass, Claude Fable subagent,
2026-09-25 (closure commits dated 2026-09-24)]. Same method and same
limits as above: read-only `git show`/`diff`/`grep`/`cmp`/`sha256sum`
from my worktree; no builds; the orchestrator's marker
`.tmp/orch-ALL-DONE` and `.tmp/orch-gates-closure.log` were both ABSENT
in the cleanup worktree when checked, so every gate line quoted from the
closure record is the remediator's CLAIM.

```
$ git log --oneline 9bb6c6b..6b20bfd
6b20bfd MUST closure F3/F4: append provenance corrections and verified F1/F5 record
292db8b M4 closure F1/F5: refuse substituted sorry types and restore recursive rep coverage
$ git merge-base --is-ancestor 38f87d5 6b20bfd && echo yes   → yes
$ git merge-base --is-ancestor 9bb6c6b 6b20bfd && echo yes   → yes
$ git diff --stat 9bb6c6b 6b20bfd
 .../2026-09-24_public-readiness-closure.md         | 92 ++++++++++++++++++++++
 .../2026-09-24_public-readiness-remediation.md     | 32 ++++++++
 src/lean_backend.ml                                |  4 +
 .../negative/neg_inline_relation_type_sorry.lem    |  6 ++
 .../negative/neg_inline_type_sorry.lem             |  5 ++
 tests/comprehensive/test_target_reps.lem           | 12 +++
 6 files changed, 151 insertions(+)
```

### (1) The `src/lean_backend.ml` +4 — PASS

Exactly the two `Typ_backend` render arms named in F1, nothing else
(verbatim from `git show 292db8b -- src/lean_backend.ml`):
```
@@ -7174,6 +7174,8 @@           (pat_typ)
         | Typ_backend (p, ts) ->
           let i = Path.to_ident (ident_get_lskip p) p.descr in
+          if String.trim (Ident.to_string i) = "sorry" then
+            raise (lean_sorry_rep_error t.locn "inline backend type");
@@ -7225,6 +7227,8 @@           (indreln_typ)
         | Typ_backend (p, ts) ->
           let i = Path.to_ident (ident_get_lskip p) p.descr in
+          if String.trim (Ident.to_string i) = "sorry" then
+            raise (lean_sorry_rep_error t.locn "inline relation backend type");
```
Both arms sit under `and pat_typ t = match t.term with` and `and
indreln_typ t = match t.term with`, so `t.locn` is the rendered
`src_t`'s location. The existing diagnostic is reused. Census of
`Typ_backend` at 6b20bfd: `:1377`, `:1469`, `:3033`, `:6668` (analysis
only), `:7175` and `:7228` (the two renderers, now guarded), `:7296`
(renders the literal `default`, not the type). No other type renderer
exists, so the two guards close the type-position route.

### (2) The two fixtures reach those sites and are wired — PASS (with a correction to my first pass)

```
neg_inline_type_sorry.lem
  (* EXPECT: forbidden (inline backend type) *)
  declare lean target_rep type nat = (`sorry`)
  type inline_hole = Hole of nat
neg_inline_relation_type_sorry.lem
  (* EXPECT: forbidden (inline relation backend type) *)
  declare lean target_rep type nat = (`sorry`)
  indreln [inline_relation : nat -> bool]
    inline_rule : forall x. true ==> inline_relation x
```
Route: the parenthesised backend type makes the declared rep a
`TYR_subst` whose `src_t` is a `Typ_backend` — bypassing the
declaration-level `TYR_simple` guard — and the substitution at a use site
(a constructor field → `pat_typ`; a relation type → `indreln_typ`) lands
on exactly the two guarded arms. The `EXPECT:` fragments are substrings of
the diagnostic ("… is forbidden (inline backend type); provide …"), matched
by `grep -qF` (`Makefile:289`); wiring is automatic through the
`negative/neg_*.lem` glob (`Makefile:284`; the Makefile is unchanged in
this range). The closure record explains why the fixtures are not the
*direct* `val x : `sorry`` form I named: that form "rejected … in the
typechecker before the renderer" (closure record `:72-75`), i.e. it is
already refused upstream of emission.

**Erratum to my first pass (R-B, appended, not rewritten):** I wrote
"`TYR_subst` carries a Lem `src_t`, so a Lean `sorry` can only enter
through a constructor whose own rep is checked". That was wrong: a
parenthesised backend type is a `Typ_backend` `src_t` directly, so a
`TYR_subst` rep can carry a bare `sorry` without any constructor. The
remediator's fixtures demonstrate exactly this; the new render-site
guards are the right place to close it.

### (3) `process_val` let-rec coverage restored with a concrete rep — PASS

`test_target_reps.lem:207-215` adds `val process_val_body : myval -> list
nat -> nat` / `let rec process_val_body v path = …` (the same
unit-match-then-tuple-match body), and `:226` adds, after the definition,
`declare lean target_rep function process_val v path = process_val_body v
path` — a parameter-binding (`CR_inline`) rep on a `let rec`, which is the
`def_trans.ml:245` `_def_lemma` trigger. `assert unit_match` is retained.
`grep -n -i sorry` over the file at 6b20bfd hits only three comment lines
(`:2-3`, `:87`); no `sorry` rep remains. The closure record's statement
that the auxiliary now contains, verbatim, `/- removed theorem
process_val_def_lemma -/` is a CLAIM not re-run here.

### (4) Appendices: verbatim [USER] rulings and the 3→23 erratum, appended — PASS

```
$ git show 9bb6c6b:…remediation.md | wc -l → 140 ;  6b20bfd → 172
$ cmp <(git show 9bb6c6b:…remediation.md) <(git show 6b20bfd:…remediation.md | head -140)
first 140 lines IDENTICAL to 9bb6c6b copy (append-only)
```
The appended `## Closure addendum — corrections and operator provenance
(2026-09-24)` (`:142-172`) states, verbatim: "The M4 row above says
"three excluded CMM reps". That is an incorrect tally: **23** target
representations were replaced by `LemUnsupported.Cmm.*` markers in
Cerberus `abe505d3d` (derived from the `frontend/concurrency/cmm_csem.lem`
diff against `e9f9d049f`). The original body is retained as the record of
the first checkpoint." Two `[USER 2026-09-24]` blocks follow with
block-quoted rulings (the M1 MUST/SHOULD split; three engagement-rule
excerpts). Cross-references verified read-only in cerberus-lean:
`abe505d3d`, `aab00b9b6`, `0a6d59eed` are commits;
`aab00b9b6:lean_frontend/docs/2026-09-24_public-readiness-must-checkpoint-orchestrator-note.md`
exists; `cmm_csem.lem` @ `abe505d3d` has 0 `` `sorry` `` reps and 23
`LemUnsupported` lines (derived) — consistent with the erratum and with
my `0a6d59eed` measurement. The 07b709e review body and the first
remediation body are untouched. New dated record
`2026-09-24_public-readiness-closure.md` (92 lines) is headed `[AGENT]`,
names its implementation pin `292db8b…`, labels its 438.45 s wall time
"not a performance claim", and records its two failed development runs
(exit 2) as not counted. Its derived "107 negative cases" = 105 + 2 (this
review's count).

### (5) Review document — PASS

```
$ git show 6b20bfd:doc/lean-backend/2026-09-24_public-readiness-review.md | sha256sum
829b78d822878242023f4354a7f29f20031ee0fd77882f206bbc8f67f7c58641  -
$ git log --oneline 07b709e..6b20bfd -- doc/lean-backend/2026-09-24_public-readiness-review.md
(no output)
```

### (6) Ancestry and pin-moving set — PASS

`38f87d5` is an ancestor of `6b20bfd` (above). Non-doc files in
`9bb6c6b..6b20bfd`: `src/lean_backend.ml` (+4, the only tool change) and
tests (`negative/neg_inline_type_sorry.lem`,
`negative/neg_inline_relation_type_sorry.lem`, `test_target_reps.lem`
+12). Docs: the new closure record and the +32 appendix. LemLib, LICENSE,
NOTICE, wrapper, Makefiles, front pages: unchanged in this range.

### Closure findings

| # | Grade | Where (at 6b20bfd) | Finding | One-line fix |
|---|---|---|---|---|
| C1 | N | `src/lean_backend.ml:2369-2390` | Declaration-level asymmetry remains: an UNUSED `TYR_simple` `sorry` type rep is refused at declaration, but an UNUSED parenthesised `TYR_subst` `sorry` type rep is refused only when a use site renders it. Emission-time fail-closed holds (nothing is emitted for an unused rep), so no live hole; symmetry only. | Walk `TYR_subst` `src_t`s for a `Typ_backend` `sorry` in `lean_sorry_rep_check`. |
| C2 | N | remediation record `:144-148` | The addendum says "checked at Lem `9bb6c6b` and Cerberus `0a6d59eed`" but attributes the 23 to `abe505d3d`; both cerberus commits exist and both carry 23 markers, so the numbers agree — the double citation is a wording wrinkle only. | None required; optional one-word clarification in a future addendum. |

F1 and F5 (first pass) are CLOSED by 292db8b; F3 and F4 are CLOSED by
6b20bfd's appendix. F2 (cerberus fork-drift prefix compare) is
cerberus-side and remains open there; F6–F10 notes stand.

## VERDICT (updated for 6b20bfd)

[AGENT] **Merge-ready as is at 6b20bfd**, conditional on the
orchestrator's independent green gate on that head (this review ran
nothing; the orchestrator's closure log and marker were absent at my
check). The closure delta is exactly the four-line render-site refusal I
asked for, two negative fixtures that demonstrably reach both sites
through the `TYR_subst` bypass (a route my first pass mis-assessed —
erratum above), a concrete-rep restoration of the `process_val`
`_def_lemma` route with no `sorry`, and an append-only remediation
appendix that carries the 3→23 erratum and two verbatim
`[USER 2026-09-24]` rulings without touching any dated body. The review
document is still byte-identical to 07b709e; `38f87d5` is still an
ancestor; the pin-moving set is `src/lean_backend.ml` plus tests. No P1,
P2 or P3 remains on the lem-lean side; two notes (C1, C2). The two-repo
sequencing fact from R-F stands: cerberus must re-pin to the final lem
head together with its `cmm_csem.lem` marker replacement. Merge authority
rests with the operator.

## Pointer — third pass (SHOULD block)

[AGENT 2026-09-25] The SHOULD-block range `6b20bfd..67ec5de` is reviewed in
a separate dated file, [`2026-09-25_public-readiness-should-delta-review.md`](2026-09-25_public-readiness-should-delta-review.md)
(different range, day and mainline base). First-pass F2 is recorded there as
closed on the cerberus SHOULD branch.
