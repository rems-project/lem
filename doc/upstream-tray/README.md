# A reader's guide for the Lem developers

This page is for the maintainers of
[rems-project/lem](https://github.com/rems-project/lem) who have been
pointed at this directory to look at the reports we have drafted against
Lem. It explains where the reports come from, how to read one, how the
reproducers were run, and what to trust. The ranked list is
[INDEX.md](INDEX.md); the drafts are the numbered files next to it.

## 1. What this repository is

`lem-lean` is a fork of Lem that adds a Lean 4 backend (`-lean`) and a
Lean runtime library (`lean-lib/`). The backend is a feature
contribution, described in `doc/lean-backend/README.md` and the manual
chapter `doc/manual/backend_lean.md`; it is not what this directory is
about. The fork's merge base with upstream is `3802cb0` (2026-05-13).

The Lean backend has been used to port two large Lem developments,
Cerberus (the C semantics) and linksem (ELF, DWARF and linking). Its
runtime is checked against Lem's OCaml target: the same programs are run
through both and their outputs compared. That comparison reads every
library function's OCaml implementation next to its Lem definition and
its prover mappings, and it found places where upstream Lem itself is
wrong or unclear, independently of Lean. Those findings were recorded in
the three projects' records; this directory collects them as reports for
you.

## 2. Our stance

Nothing here asks you to adopt the Lean backend. Every report stands on a
reproducer run on unmodified upstream `3802cb0`, needing only `lem`, the
OCaml compiler and zarith. Where the fork had already fixed something in
target-independent code, the draft proposes that fix as its remedy
(section 5). The classifications are our reading; where we could
not tell what you intended, the draft is a question.

## 3. How to read a draft

Each draft is a self-contained issue report with:

- **Title**, **target** and **affected code**, cited as `file:line` at
  upstream `3802cb0`, with a note where the fork's copy differs.
- **Classification**: **TRUE BUG** (the code's evident intent and its
  behaviour disagree), **INTENDED GAP** / **KNOWN LIMITATION** (the
  behaviour is acknowledged in a comment or name; reported because its
  consequence seemed worth raising), or **UNCLEAR** (a question). Each comes
  with its justification.
- **Reproducer**: a short `.lem` file, often with a small OCaml driver
  that prints the values.
- **Verbatim output** with its capture date and build (section 4).
- **Observed vs expected**, **impact**, and a **proposed remedy** (a
  suggestion, not a demand).
- **Origin**: where the finding was first recorded, with any decision
  recorded in the agent's own words and tagged `[USER]` (the human operator) or `[AGENT]`
  (an AI agent).
- **Provenance**: how the finding was made (section 7).

## 4. How the reproducers were run

All runs: 2026-10-03, on an unmodified upstream checkout at `3802cb0`
built with its own `make` (`lem -v` prints `Lem 3802cb0`), OCaml 5.4.0,
zarith 1.14. The OCaml runtime was upstream's `ocaml-lib`, compiled in a
scratch directory from the same checkout (the generated `lem_*.ml` were
first regenerated from upstream `library/` with upstream `lem` and found
byte-identical). No fork code was involved in any run, except the
checks of the fixes in drafts 01 and 03, which used local patched builds
of `3802cb0` (since deleted, §5) and say so.

The sources and full transcripts are in [`repro/`](repro/): one directory
per reproducer, holding the `.lem` file, any driver, and
`transcript-2026-10-03.txt`. [`repro/run-all.sh`](repro/run-all.sh)
re-creates every transcript (see [`repro/README.md`](repro/README.md));
[`repro/run.sh`](repro/run.sh) is the per-reproducer step for the OCaml
cases.

Transcript conventions: lines starting `$ ` and lines like `[lem exit 0]`
or `[exit 2]` are printed by the scripts, not by the tools; the
`ocamlopt` command line is abbreviated as `-I <upstream ocaml-lib>
extract.cmxa`. Everything else is tool output, pasted, never retyped. A
draft that quotes only part of a transcript says "excerpt" and names the
file.

## 5. No patch branches

This tray prepares reports, not pull requests ([USER 2026-10-03] ruled out upstream-PR writing and had the patch branches deleted). Drafts 01 and 03 describe a fix that was
built and checked on a local branch (since deleted); the reports carry the
fix as a proposed remedy.

## 6. Triage at a glance

| Draft | Summary | Class |
|---|---|---|
| 01 | Block-formatted output decoded as Latin-1; OCaml string literals in compiled patterns change value | TRUE BUG (fix proposed) |
| 02 | Comments decoded as Latin-1: `§` → `Â§` on every backend | TRUE BUG |
| 03 | A missing `<target>_constants` silently disables renaming | TRUE BUG (fix proposed) |
| 04 | `Assert_extra.fail "msg"` prints as invalid OCaml | TRUE BUG |
| 05–09 | OCaml `mword` runtime: `getBit`, negation of 0, `setBit` beyond width, rotations/shifts raising, widths from arguments | TRUE BUG |
| 10 | OCaml `int` div/mod by a negative divisor; `integer` convention | TRUE BUG + UNCLEAR |
| 11 | OCaml default `max`/`min` ignore `Ord` instances | TRUE BUG |
| 12 | `Set.splitMember` halves swapped | TRUE BUG |
| 13 | OCaml `=` on values containing sets/maps raises | KNOWN LIMITATION / question |
| 14–16 | `THE` OCaml rep; `transform.lem` broken; `defaultLnot` negates | TRUE BUG (minor) |
| 17–18 | OCaml `replicate` stack depth; `genlist` quadratic | TRUE BUG (robustness/performance) |
| 19–20 | 31-bit `int`/`nat` bitwise definitions; `bigunionBy` comparator | UNCLEAR |
| 21 | `wordToHex` stub | INTENDED GAP |
| 22 | 63-bit `nat`/`int` on OCaml | note |
| 23 | Comments before `and` in mutual definitions dropped (Coq; Isabelle/HOL4 when matches are lifted) | TRUE BUG (minor) |

## 7. How this work was produced

The fork, its records and these drafts were produced by AI agents
(Claude, Anthropic) working under the direction and review of a human
operator. Each draft's classification is proposed by the drafting agent;
the operator decides what is filed. Any filed issue will say how the
finding was made (INDEX.md, "Provenance
labelling").

## 8. Caveats

- **The pin is dated.** Please re-run a reproducer on current `master`
  before acting on it; we had no network access when drafting and did not
  check master.
- **No duplicate search** has been done for any draft.
- **Prover-side expectations** (HOL4, Isabelle, Coq) are read from the
  definitions the library maps to; no prover was run.
- **Two earlier copies exist**: drafts 04 and 13 were first written in the
  linksem and Cerberus repositories; those copies stay as they are
  (INDEX.md, "Origin cross-reference").

## 9. How to respond

Issues or comments on this repository are welcome, as are replies on any
issue we file upstream. The repository owner is the contact.
