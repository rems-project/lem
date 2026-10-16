# Upstream Lem report drafts — index

> Lem developers: start with [README.md](README.md), the reader's guide to
> this directory.

Draft reports against [rems-project/lem](https://github.com/rems-project/lem)
found while building and using the Lean 4 backend in this repository.
Every citation is to upstream `3802cb0` (2026-05-13, the merge base of
this fork), and every reproducer was run on 2026-10-03 against an
unmodified upstream `3802cb0` build. Filing is the operator's call; nothing
here has been submitted.

## Submission status

**Draft** = prepared, no recorded submission; **Sent** = transmitted
without an issue URL; **Filed** = issue URL recorded; **Closed** =
upstream closure recorded.

Inventory (2026-10-03): 23 reports, **23 Draft, 0 Sent, 0 Filed, 0
Closed**; no patch branches (README §5). Draft 23 was added
later the same day (orchestrator finding).

| Report | Recorded state | Submission evidence |
|---|---|---|
| [01-block-formatted-output-double-utf8-encoding.md](01-block-formatted-output-double-utf8-encoding.md) | Draft | No submission recorded |
| [02-comment-text-decoded-as-latin1.md](02-comment-text-decoded-as-latin1.md) | Draft | No submission recorded |
| [03-reserved-name-lists-loaded-fail-open.md](03-reserved-name-lists-loaded-fail-open.md) | Draft | No submission recorded |
| [04-assert-extra-fail-applied-prints-invalid-ocaml.md](04-assert-extra-fail-applied-prints-invalid-ocaml.md) | Draft | No submission recorded |
| [05-mword-getbit-reads-bits-i-to-2i.md](05-mword-getbit-reads-bits-i-to-2i.md) | Draft | No submission recorded |
| [06-mword-negation-of-zero-not-reduced.md](06-mword-negation-of-zero-not-reduced.md) | Draft | No submission recorded |
| [07-mword-setbit-beyond-width-not-masked.md](07-mword-setbit-beyond-width-not-masked.md) | Draft | No submission recorded |
| [08-mword-rotations-and-arith-shifts-raise.md](08-mword-rotations-and-arith-shifts-raise.md) | Draft | No submission recorded |
| [09-mword-width-taken-from-value-not-type.md](09-mword-width-taken-from-value-not-type.md) | Draft | No submission recorded |
| [10-int-div-mod-negative-divisor.md](10-int-div-mod-negative-divisor.md) | Draft | No submission recorded |
| [11-default-max-min-structural-on-ocaml.md](11-default-max-min-structural-on-ocaml.md) | Draft | No submission recorded |
| [12-set-splitmember-halves-swapped.md](12-set-splitmember-halves-swapped.md) | Draft | No submission recorded |
| [13-structural-equality-on-set-values-raises.md](13-structural-equality-on-set-values-raises.md) | Draft | No submission recorded |
| [14-the-ocaml-rep-names-no-value.md](14-the-ocaml-rep-names-no-value.md) | Draft | No submission recorded |
| [15-transform-library-does-not-typecheck.md](15-transform-library-does-not-typecheck.md) | Draft | No submission recorded |
| [16-defaultlnot-negates-instead-of-complementing.md](16-defaultlnot-negates-instead-of-complementing.md) | Draft | No submission recorded |
| [17-list-replicate-not-tail-recursive.md](17-list-replicate-not-tail-recursive.md) | Draft | No submission recorded |
| [18-list-genlist-quadratic.md](18-list-genlist-quadratic.md) | Draft | No submission recorded |
| [19-int-nat-bitwise-31-bit-definitions-question.md](19-int-nat-bitwise-31-bit-definitions-question.md) | Draft | No submission recorded |
| [20-bigunionby-comparator-ignored-question.md](20-bigunionby-comparator-ignored-question.md) | Draft | No submission recorded |
| [21-wordtohex-stub.md](21-wordtohex-stub.md) | Draft | No submission recorded |
| [22-nat-int-63-bit-on-ocaml-note.md](22-nat-int-63-bit-on-ocaml-note.md) | Draft | No submission recorded |
| [23-comments-before-and-dropped-in-mutual-definitions.md](23-comments-before-and-dropped-in-mutual-definitions.md) | Draft | No submission recorded |

## Ranking and triage (by upstream value) [AGENT]

The numbering is the ranking: true bugs that silently change output or
values first, then crashes and invalid output, then minor and robustness
bugs, then questions, gaps and the note. Ranking proposed by the drafting
agent for the operator to adjust.

| # | One-line summary | Class | Reproduced on `3802cb0` | Patch branch (none: see README §5) |
|---|---|---|---|---|
| 01 | Block-formatted output decoded as Latin-1: string literals in compiled patterns change value on OCaml | TRUE BUG | yes | — |
| 02 | Comment text decoded as Latin-1: `§` → `Â§` on every backend | TRUE BUG | yes | — |
| 03 | Missing `<target>_constants` silently empty: renaming off, invalid output | TRUE BUG | yes | — |
| 04 | `Assert_extra.fail "msg"` prints `(assert false "msg")`, invalid OCaml | TRUE BUG | yes | — |
| 05 | OCaml `getBit w i` tests bits `i..2i` | TRUE BUG | yes | — |
| 06 | OCaml `uminus 0 = 2^n` (also `wordFromInteger`, `signedDivide`) | TRUE BUG | yes | — |
| 07 | OCaml `setBit` beyond the width stores an out-of-range value | TRUE BUG | yes | — |
| 08 | OCaml rotations by 0 / by the width / beyond, and wide `asr`, raise | TRUE BUG | yes | — |
| 09 | OCaml `wordFromBitlist`/`word_extract`/`word_concat` width from arguments, not type | TRUE BUG (design component) | yes | — |
| 10 | OCaml `int` div/mod by a negative divisor neither floor nor Euclidean; `integer` Euclidean vs provers' floor | TRUE BUG + UNCLEAR | yes | — |
| 11 | OCaml default `max`/`min` are structural, ignoring `Ord` instances | TRUE BUG | yes | — |
| 12 | `Set.splitMember` halves swapped relative to `split` | TRUE BUG | yes | — |
| 13 | OCaml `=` on a type containing a set/map raises `compare: functional value` | KNOWN LIMITATION / question | yes (first execution) | — |
| 14 | `THE` represented as a non-existent OCaml name | TRUE BUG (minor) | yes | — |
| 15 | `library/transform.lem` does not type-check (`find_non_pure`) | TRUE BUG (minor) | yes | — |
| 16 | `defaultLnot` negates instead of complementing (unused in the library) | TRUE BUG (minor) | yes | — |
| 17 | OCaml `replicate` not tail-recursive: `Stack overflow` | TRUE BUG (robustness) | yes | — |
| 18 | OCaml `genlist` quadratic (`snoc`) | TRUE BUG (performance) | yes | — |
| 19 | `int`/`nat` bitwise ops 31-bit by definition (provers) vs 63-bit on OCaml | UNCLEAR (question) | yes (definitions executed on OCaml) | — |
| 20 | OCaml `bigunionBy cmp` ignores `cmp` | UNCLEAR (question) | yes (behaviour as described; not a wrong value) | — |
| 21 | `wordToHex`/`show` on machine words is a stub on OCaml/Isabelle/Coq | INTENDED GAP | yes | — |
| 22 | `nat`/`int` 63-bit and silently wrapping on OCaml (a `nat` can be negative) | INTENDED GAP (note) | yes | — |
| 23 | Comments before `and` in `let rec … and …` dropped (Coq always; Isabelle, HOL4 `-hol_remove_matches` when matches are lifted, which also reorders clauses) | TRUE BUG (minor, output fidelity) | yes | — |

Draft 23 was added after the ranking and is numbered last; by value it
belongs with the minor true bugs (14–16) [AGENT].

Every reproducer reproduced. "Reproduced" means the upstream `3802cb0`
build shows the behaviour the draft describes; for 19 and 20 the drafts
are questions, and for 22 the behaviour is documented upstream.

## Scope: what "All 16" became, and what was left out [AGENT]

The operator's ruling ([USER 2026-10-03], recorded in lem-lean
`doc/lean-backend/2026-10-03_output-niceness-arc-plan.md` §3, branch
`arc/output-niceness` at `b8bf958`): tray scope is all 16 findings, re-verified —
every upstream-Lem finding recorded in the Cerberus, linksem and lem-lean docs
gets a draft, including the five that are only on the archive branch
`archive/linksem-fixes-2026-09-30` and the machine-word findings.

The count does not reconcile exactly with the survey that preceded it,
so this tray follows the ruling's every-finding wording rather than the
number. The survey listed 16 numbered items (the five machine-word OCaml
findings OM1–OM5 as separate items) plus the five archive-only ones,
which is 21; the operator was told 16 "including the five archive-only
ones". One grouping that gives 16, offered as a guess only: the 63-bit
note left out and OM1–OM5 counted as one finding. This tray had 22
drafts at that point (draft 23 came later, from a new finding): those 16, plus OM1–OM5 split into five drafts (05–09, +4), the
63-bit note (22, +1), and one item the survey listed as ambiguous that
proved to be an upstream defect (01, +1).

Mapping from the survey's numbering to drafts: 1→13, 2→04, 3→22, 4→03,
5→18, 6→17, 7→10, 8→19, 9 (OM4)→09, 10 (OM1)→06, 11 (OM2)→05, 12
(OM3)→07, 13 (OM5)→08, 14 (LP5)→21, 15→15, 16→02; archive-only LU1→12,
LU2→16, LP1→11, LP9→20, THE→14; ambiguous `output.ml` UTF-8 decode→01.

Considered, not upstream (no draft):

- lem-lean review `2026-08-31_backend-quality-review.md` m3(a), m3(b),
  m3(d): the fork's edits to shared code in `src/target_binding.ml`
  (`search_module_suffix` falls back to the global environment),
  `src/typed_ast_syntax.ml` (class paths renamed and recorded as used
  entities) and `src/target_trans.ml` (`add_avoid_type` returns its input
  where upstream raised). They came in with the fork's Lean work
  (e.g. `2345f24` "Fix cross-module constant resolution, …, add
  lean-libs"; `0b59281` "Support declare rename for classes; add Eq/Eq0
  and Ord/Ord0 renames"); no upstream behaviour they would fix has been
  shown on `3802cb0` (checked by reading only), and m3(d) is the fork's
  own fail-open conversion, a fork defect. Only m3(c), the `output.ml` decode,
  reproduces on upstream (draft 01).
- Library-parity findings that concern only the fork's Lean target (LP2,
  LP3, LP6, LP7, LP8 in the archived record `8ccbe40`): fork defects,
  fixed or recorded in lem-lean.

## Origin cross-reference

| Draft | Recorded first in | Copy elsewhere |
|---|---|---|
| 01 | lem-lean `doc/lean-backend/2026-08-31_backend-quality-review.md` m3(c); fix in lem-lean `c515e6d` | — |
| 02 | Cerberus branch `docs/next-phase-plan-20260925`, `lean_frontend/docs/2026-09-25_next-phase-plan.md` §1.6 | — |
| 03 | lem-lean `doc/lean-backend/2026-09-28_linksem-findings.md` §B10; fix in lem-lean `8c3a4ca` | — |
| 04 | linksem `lean/docs/upstream-tray/lem/01-assert-extra-fail-applied-prints-invalid-ocaml.md` (`9cafe16`) | **that draft remains as a copy, unchanged** |
| 05–09 | lem-lean archived record `8ccbe40` §2 OM2, OM1, OM3, OM5, OM4; mainline `doc/lean-backend/2026-09-30_library-parity-coverage.md` §1–§2 | — |
| 10 | lem-lean `doc/lean-backend/2026-09-03_parity-fix-record.md` §F1; archived record `8ccbe40` "F1 note" | — |
| 11, 12, 16, 20, 14 | lem-lean archived record `8ccbe40` §2 LP1, LU1, LU2, LP9, THE (14 also parity-fix record row X5) | — |
| 13 | Cerberus `lean_frontend/docs/upstream-tray/lem/01-polymorphic-compare-on-set-values.md` (`56ab39ea0`); lem-lean parity-fix record row X1 | **the Cerberus draft remains as a copy, unchanged** (its output section was never run; draft 13 has the first run) |
| 15 | lem-lean mainline `doc/lean-backend/2026-09-30_library-parity-coverage.md` §2 ("`lnot` at `nat`") | — |
| 17 | Cerberus `lean_frontend/docs/2026-09-01_mem-scale-design.md:340-343` | — |
| 18 | lem-lean `doc/lean-backend/TODO.md` item 7; parity-fix record §F9 | — |
| 19 | lem-lean mainline library-parity record §1 LP4 | — |
| 21 | lem-lean mainline library-parity record §2 item 1 (LP5) | — |
| 22 | Cerberus `lean_frontend/docs/upstream-tray/lem/README.md` (the 63-bit note); lem-lean `doc/lean-backend/2026-09-03_exception-case-rulings.md` X3/N4 | the Cerberus README keeps its note |
| 23 | lem-lean orchestrator, 2026-10-03 (output-readability work), reported to this slice with the `test_and.lem` reproducer | — |

The Cerberus and linksem `lem/01` drafts stay where they are, untouched
([USER 2026-10-03]: the tray's home is lem-lean and the copies stay). If one of those
reports is filed, record it in both places.

## Fixes checked locally (no patch branches)

Each fix was built on a local branch based directly on upstream
`3802cb0` (since deleted, README §5). On each, `make` (bin/lem, every
library backend, ocaml-lib and its tests) was run
on 2026-10-03 and succeeded, and the 145 library files Lem generates
(29 OCaml, 29 HOL4, 29 Isabelle, 58 Coq: those marked "Generated by Lem")
are byte-identical to unpatched `3802cb0`'s. (An earlier version of this
tray said 150: that count also included five hand-written, tracked files
in the same directories, `ocaml-lib/lem.ml`, `hol-lib/lemScript.sml`,
`isabelle-lib/Lem.thy`, `isabelle-lib/LemExtraDefs.thy` and
`coq-lib/coqharness.v`, which no build rewrites; corrected 2026-10-03
after an independent verifier's recount.)

- Draft 01: one line in `src/output.ml`.
- Draft 03: `src/initial_env.ml`, the target-independent part of lem-lean
  `8c3a4ca` adapted to upstream's targets.

These fixes were built and checked on local branches that were then
deleted ([USER 2026-10-03] ruled out upstream-PR writing and had the branches deleted; README §5).

No other finding has an existing fix to adapt.

## Provenance labelling

Following the policy the Cerberus tray uses for the same upstream group
([USER 2026-08-23] in Cerberus `upstream-tray/INDEX.md`): every issue
filed from this tray carries an explicit note that the finding was made
by AI agents (Claude, Anthropic) under human direction.

## Filing checklist (operator; needs network and GitHub)

For each draft, in ranking order:

1. Re-run the reproducer against current upstream `master` (ours is
   pinned at `3802cb0`; no network was available when drafting, so
   master was not checked).
2. Search the upstream issue tracker for duplicates (not done for any
   draft).
3. File with the draft's title, reproducer, verbatim output,
   classification and remedy; questions (19, 20) and the note (22) as
   questions or not at all.
4. For 01 and 03, include the proposed fix in the issue text; no pull
   request is prepared (README §5).
5. Record the issue URL in the draft header and in the status table
   above; if the draft has a copy in Cerberus or linksem, there too.
6. Apply the provenance labelling above.

## Caveats

- **Pin.** All runs are on `3802cb0`; upstream master may have moved.
- **Prover columns not executed.** Where a draft states what HOL4,
  Isabelle or Coq compute, that comes from the definitions the library
  maps to; no prover was run (each draft says so).
- **Line numbers.** The survey behind this tray cited several library
  lines from lem-lean's copies (e.g. `list.lem:590-591`, `set.lem:400`,
  `word.lem:743`, `basic_classes.lem:260,264`, `num.lem:104-111`); the
  drafts cite upstream's lines and give lem-lean's where they differ.
- **Generated files.** `ocaml-lib/lem_*.ml` are generated and untracked
  upstream; the OCaml runtime used was regenerated from upstream's
  `library/` with upstream `lem` and found byte-identical to the
  checkout's copies before compiling.
- **Timings** (17, 18) are single runs on a shared machine.
