# Docs release-hygiene record — 2026-09-02

Provenance: docs worker slice [AGENT], branch `docs/release-hygiene`
off mainline `mdd/lean-backend` @ `045dcb0`, worktree
`worktrees/lem-lean-docs/release-hygiene`. Brief: the 2026-09-02
release-quality sweep found stale, reasoning-era or false statements in
this repo's shop-window docs; the operator ruled [USER 2026-09-02] that
the semantics product's trust surface must read as an obviously
right Lean port of Cerberus, with reasoning-era machinery gone
(runEffectful axiom DELETED 2026-09-01; DAEMON long gone; effect
erasure retired). Governing standard: shop-window docs describe the
system AS IT IS; history lives in dated records. Scope: docs + one
comment change in the shipped library; NO backend code changes; NO
merge; NO push. Quoted outputs are verbatim; judgment calls are marked
[AGENT].

## Commits (in order)

| Item | Commit | Disposition |
|---|---|---|
| 2 | `dc1c41b` | `lean-lib/LemLib.lean` HISTORY comment — REWRITTEN to the live enforcer (comment-only; LemLib build green) |
| 1 + 3 | `d47e2a7` | README/DESIGN PROOF.md + kernel-theorem pointers — REWRITTEN; DESIGN pipeline paragraph's "effect boundary" — FIXED (extra, [AGENT]); notes banner — second supersession line APPENDED |
| 4 | `47e59b1` | `doc/manual/backend_lean.md` — REWRITTEN to current behavior (m5) |
| 5 | `fb0c6e5` | `doc/lean-backend/TODO.md` backlog register — CREATED; README pointer ADDED; `.gitignore` negation for the register (see §Item 5) |
| — | (this record's commit) | record |

## Item 1 — README:59-60 and DESIGN:250-253 (`d47e2a7`)

Verified the cites: `doc/lean-backend/README.md:60` read
`` `lean_frontend/PROOF.md` and `DESIGN.md`.) `` and
`doc/lean-backend/DESIGN.md:250-253` read "The largest deployment of
that bet is the cerberus-lean project, whose kernel theorems about C
programs run through this backend's output — its
`lean_frontend/PROOF.md` documents the resulting trust story from the
consumer side." `cerberus-lean/lean_frontend/PROOF.md` does not exist
(`ls` → `No such file or directory`); `lean_frontend/VALIDATION.md`
does, and opens "VALIDATION — why you should trust this semantics".

Rewritten: README points at `lean_frontend/VALIDATION.md` ("what is
compared, against what, and what its gates guarantee") and
`lean_frontend/DESIGN.md`. DESIGN's closing section is retitled "Why
this makes generated code trustworthy" and names the consumer as an
executable Lean port of the Cerberus C semantics, generated from the
same Lem model as the OCaml implementation and validated differentially
against it, with VALIDATION.md as the trust story. The word "prover"
survives only as one of three possible consumers of the same
properties (total functions, real instances, zero axioms, loud
failure) — those properties are true of the output regardless of
consumer.

Extra finding [AGENT], fixed in the same commit: `DESIGN.md:23-24`
("numeric/string bridges, and the effect boundary (below)") still
listed the RETIRED effect boundary as a LemLib component the generated
code imports. Now "the supply-threading split (`supplySplit`, below)".

Left as-is, flagged: `DESIGN.md` §"The effect boundary is RETIRED"
(lines ~76-97) is a correct statement of the current state but carries
a paragraph of narrative history ("The historical resolution ... The
effect-retirement arc DELETED that mechanism end-to-end ... because
..."). Out of this brief's item list; under the shop-window standard it
is a candidate for trimming to one sentence + a pointer at the next
DESIGN.md review. Not changed here.

`README.md:17-22` ("You want the generated code to be **reasoned about
in Lean** — the backend's design choices (below) exist to keep
generated code proof-friendly") was judged [AGENT] a true statement
about the backend's design (fuel totality, zero axioms, real
instances), not a claim about a consumer's theorems; kept.

## Item 2 — LemLib.lean:28-29 comment (`dc1c41b`)

Verified: the comment read "consumers enforce absence in-build
(cerberus-lean relsem/RelSem/Audit.lean absence gate)";
`cerberus-lean/relsem` does not exist (`ls` → `No such file or
directory`). The live enforcer `cerberus-lean/scripts/check_theorem_axioms.sh`
exists; its header states "since arc-8 S3 the DAEMON axiom family is
DELETED from LemLib and the toggle is gone — DAEMON is unconditionally
fatal in every probed cone", "sorryAx remains forbidden everywhere
probed", and it runs a hand-written axiom census plus a tree-wide
`generated/` census. Comment now names that script and what it does.
Comment-only: no declaration in the file changed. Consumers pick the
new text up at their next pin bump (no functional change).

Gate (verbatim, `CERB_MEM_MAX=32G capped lake build` in `lean-lib/`):

    Build completed successfully (35 jobs).

## Item 3 — effectful note banner (`d47e2a7`)

`doc/notes/2026-04-12_effectful_target_reps.md:1` still says "The
shipped design refines its Option 3: `declare {lean} effectful val`
marks the rep ... through the single library axiom
`LemLib.runEffectful`". Append-only: the existing line is untouched; a
second blockquote line "SUPERSEDED AGAIN (2026-09-01, effect-retirement
arc L2)" is inserted after it, stating the deletion, the fail-closed
refusal, the supply-lifting replacement, and pointing at
`2026-09-01_L2-deletion-record.md` and `DESIGN.md`.

## Item 4 — the m5 manual rewrite (`47e59b1`)

Verified the stale claims at the cited lines before rewriting:
`:40-42` and `:78` DAEMON axiom / `noncomputable instance`; `:37` and
`:80` `sorry`-based stub instances / "`sorry` for undefined/opaque
terms"; `:53-59` `declare {lean} effectful` + `runEffectful(...)` call
wraps; `:25` "Lemmata and theorems generate `theorem` declarations with
`by decide`" — the code (`src/lean_backend.ml` `def_extra`,
`Lemma_lemma`/`Lemma_theorem` arm) emits `/- removed theorem NAME -/`.
Absent from the old chapter: `fuel` (both forms), `reader`,
`reader_seed`, `reader_consumer`, `supply`, `ground_rep`.

Authoritative annotation list taken from `src/lexer.mll:133-142` and
the `declaration` productions of `src/parser.mly` (`Declare
targets_opt <Word> ...`): `termination_argument`, `skip_instances`,
`extra_import`, `effectful` (retired on lean), `reader`, `fuel`
(BacktickString sentinel row and Num budget row), `ground_rep`,
`reader_seed`, `supply`, `reader_consumer`; plus the upstream `rename`
and `target_rep` forms. Mechanism semantics from `DESIGN.md` and the
L1 record; guard wording from the `EXPECT` headers of the 41 probes in
`tests/comprehensive/negative/` (every probe cited by name in the
chapter was matched to its `EXPECT` line).

New section map (headings, in order):

1. Lean 4 (intro: `-lean`, the two files, `lean` vs `{lean}` declare forms, the design intent)
2. Compilation
3. What the Lean target emits
4. Auxiliary Files
5. Recursive Definitions and Totality (partial default; `termination_argument`; fuel sentinel form; fuel budget form; guards → probes)
6. Inductive Relations
7. Machine Words and Fixed-Width Integers
8. Comparison Instances (BEq/Ord parity; set/map trio; Type-1 rejection; the priority table)
9. Inhabited Instances
10. Failure Sites and the Runtime's Loud-Failure Machinery (zero axioms; `failwithI`, `fuelExhausted[With]`, `supplySplit`; the only two opaque/implemented_by pairs; `LEAN_ABORT_ON_PANIC`)
11. Target Representations and Ground-Typed Heads (`ground_rep`)
12. Reader Lifting (`reader`, `reader_seed`, `reader_consumer`)
13. Supply Lifting (`supply`)
14. Skipping Instance Generation
15. Extra Imports
16. Automatic Renaming (incl. the reserved-name contract)
17. Contextual Keywords
18. The Retired `effectful` Annotation
19. Set Comprehensions
20. What Other Targets Can Rely On (`make nonlean-regress`; `lean-invariance`)
21. Testing the Backend (the `make lean` phases; the negative suite as executable spec)
22. Known Limitations (L1 deviations; paren-split spine strictness; `sorry` target_rep pass-through; int32/int64; ground_rep coverage)
23. Relationship to Coq Backend
24. Further Reading (the one pointer paragraph to the dated records)

Sections 2, 6, 7, 14, 15, 23 keep the old chapter's structure and
text where still right; 4 and 16 keep the structure with corrected
content.

Claims verified against code beyond DESIGN.md (file cites): `«»`
keyword escaping and the keyword list (`lean_backend.ml:142-157`);
`Lem_` namespaces (`:771-777`); indexed families in `Type 1`
(`:5013-5032`); assertions as `#eval do ... PASS/FAIL` and theorems as
comments (`def_extra`); `termination_argument automatic` → `def`
(`:2773-2790`); `ground_rep` ground-site substitution with type
ascription (`:2079-2085`, `:3999-4008`) and its supply guard
(`:3790-3791`); the `Backend "sorry"` pass-through (`:4044-4050`);
reader parameter sorted-name order (`:526-537`, `List.sort ...
String.compare`); the reader/seed/consumer guard messages (`:481-502`,
`:2575`, `:2903-2926`, `:3654`); the effectful refusal message
(`:462`); Lean avoid-set = all type names in scope + class names
(`src/rename_top_level.ml:274-285`, `src/target_trans.ml:462-470`);
`mword` → `BitVec` (`library/machine_word.lem:23`); `int32`/`int64` →
`LemInt32`/`LemInt64` newtypes over `Int` with unbounded arithmetic
(`library/num.lem:174,182`, `lean-lib/LemLib.lean:719-729`); the
opaque/`implemented_by` census of the library (exactly `failwithI` /
`failwithIImpl` and `fuelExhaustedWith` / `fuelExhaustedWithImpl`;
zero `axiom` lines); `-auxiliary_level none|auto|all`
(`src/main.ml:159-166`); the `lean-negative`, `lean-panic`,
`lean-invariance` phase mechanics (`tests/comprehensive/Makefile`);
`expected_failures.txt` has no non-comment entries.

Dropped as NOT verifiable against the code [AGENT]: the old chapter's
specific list of "names that clash with Lean 4 standard library type
classes (such as `Add`, `Sub`, `Neg`, `Mul`, `Div`, `Mod`, `Pow`,
`Min`, `Max`, `Abs`, `Not`, `Append`)" said to be automatically
renamed — no such list exists in `src/` (`grep` for the quoted names
in `src/*.ml` → no hits). The chapter now states what the renaming
pass actually does (all type and class names in scope go into the Lean
avoid set).

Claims carried from records rather than re-measured here (each cites
its record in the chapter or above): the short-circuit preservation
under supply threading and the paren-split strictness (L1 addendum
MAJOR-1; audit log NOTE-1; L2 rider (a)); the L1 deviations (L1 record
§Deviations 3-5); NOTE-3 (fuel budget on a zero-arg value → vacuous
wrapper). No claim in the chapter was written without either a code
cite or a record cite; none had to be marked "unverified".

## Item 5 — backlog register (`fb0c6e5`)

`doc/lean-backend/TODO.md` created with six priced items (sources
cited per row) plus the un-actioned S-class notes from the quality
review. README.md's Status paragraph now says "registered in TODO.md"
(was "tracked in the dated notes") and the Pointers paragraph lists
TODO.md and the manual chapter.

Source-attribution note [AGENT], recorded in the register itself: the
brief attributes "refuse a `sorry` target_rep" to a "cerberus fuel-arc
rider". That phrasing was not located in either repo's records (grep
over cerberus-lean `lean_frontend/docs/` and `TODO.md`, and this
repo's `doc/`). The item IS registered, at: quality review m6 (this
repo), cerberus-lean `2026-08-20_arc10-s0-triage.md` row 19 ("standing
TEMPORAL entry; mover = concurrency arc") and `2026-08-20_arc8-results.md`.
Those are the cites given. The live consumer use is
`cerberus-lean/frontend/concurrency/cmm_csem.lem:663`
(`observable_filter = `sorry``), surfacing as `(sorry : String)` in
`generated/Cmm_op.lean:292`.

`.gitignore` finding [AGENT], fixed in the same commit: the fork-added
"Local files" rule (`.gitignore:64`, `TODO.md`) ignores every
`TODO.md` repo-wide, so the new register was silently untracked
(`git status` did not list it; `git check-ignore -v` →
`.gitignore:64:TODO.md`). Added a commented negation
`!doc/lean-backend/TODO.md` directly under the rule — a structural fix
rather than a one-off `git add -f`, so a future re-creation cannot
silently fall through. This is the only non-`doc/` file touched besides
`LemLib.lean` (item 2). Operator attention: if the intent of the rule
was to ignore ALL TODO files as a matter of policy, the register should
be renamed instead; [AGENT] judged the brief's explicit filename as
governing.

## Item 6 — verification (at `fb0c6e5`, docs tree; all commands via `scripts/ce` / `capped`)

Root `make` (worktree lem rebuilt before trusting tests): `MAKE EXIT: 0`.

`tests/comprehensive`: `CERB_MEM_MAX=32G capped make lean` →
`COMPREHENSIVE MAKE EXIT: 0`. Verbatim gate lines:

    === Generation: 47 passed, 0 failed, 0 skipped ===
    Build completed successfully (134 jobs).
      OK (leg 1): panic prints the Incomplete Pattern message, then continues with default
      OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1
      OK: draws: first=1 second=2
    single-evaluation: OK
      OK: parity holds (Euclidean, both targets)
      OK: compiled draw sequences hold
      OK: compiled consumer injection holds
      OK: budgeted cut at 5; unannotated at the exact lemDefaultFuel boundary
      OK: inv_fuel_budget.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
      OK: inv_reader_consumer.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
      OK: inv_supply.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)

Negative probes: 41 rows `OK (rejected as declared)` (derived count,
`grep -c` over the run log); 0 rows containing `FAIL`.

`lean-lib`: `CERB_MEM_MAX=32G capped lake build` →
`Build completed successfully (35 jobs).` (the item-2 comment change is
the only library delta).

`make nonlean-regress` (verbatim):

    nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)

Zero golden updates; no emitter touched.

The comprehensive and nonlean runs were executed on the working tree
carrying all item 1-5 edits (docs cannot affect them; the `.gitignore`
edit does not either). Suite log kept at the container's ephemeral
`.tmp/` during the slice; every load-bearing line is quoted above.

## Slice state

- Branch `docs/release-hygiene` @ this record's commit; 5 commits over
  `045dcb0` (`dc1c41b`, `d47e2a7`, `47e59b1`, `fb0c6e5`, + record).
- Worktree clean after the record commit.
- NO merge, NO push, NO pin bumps. Consumers see the LemLib comment at
  their next Lake pin bump; no functional delta is carried.
- Files touched outside `doc/`: `lean-lib/LemLib.lean` (comment only),
  `.gitignore` (one negation line + comment).
