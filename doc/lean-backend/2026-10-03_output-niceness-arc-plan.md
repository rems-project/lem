# Output-niceness arc: plan and rulings (2026-10-03)

Branch `arc/output-niceness`, from `mdd/lean-backend` at `6e2526e`.

## 1. Trigger

Feedback from a Lem developer after reading linksem's `src/dwarf.lem` next to
the generated `Dwarf.lean` (relayed by the operator, 2026-10-03; paraphrased):
the Lean output had lost many of the source comments; comments added by the
translation were not marked as such; there were extra blank lines between
inductive cases; some Lem record types became readable Lean while others (for
example `sdt_subroutine`) became a single-constructor inductive taking a long
list of positional arguments, which looked bad though the developer was unsure
what idiomatic Lean would force (for example for mutual recursion through
records); and a build needing more than 20G of memory, as an agent's note had
described, looked suspicious.

Operator direction [USER 2026-10-03]: fix these specific things, then do a
general niceness pass to make the output nice and reasonable; and later in
the same session: rationalise the docs, make sure the TODO list is clean,
and lift the lem-upstream findings documented in linksem and cerberus into
lem, using cerberus's tray style.

## 2. Measurements (2026-10-03, lem `6e2526e`; [AGENT])

The trees are linksem's 96 model modules and Cerberus's 85 Lean-built `.lem`
files, regenerated with `lem` at `6e2526e`. linksem's checked-in
`lean/generated/` is identical to this regeneration, apart from two stale
`Dump_image*` files.

1. **Comments lost (Lean only).** A scan counted the top-level `(* … *)`
   comments in `dwarf.lem` and searched for each comment's alphanumeric
   text in the output.
   - `Dwarf.lean` is missing 87 of 797 comments.
   - The OCaml backend's `dwarf.ml` is missing 1, a nested comment the scan
     mis-reads.

   Comments are lost at four kinds of site:
   - in front of a removed `val` or `declare`, which is how the module's
     header essay is lost. `Val_spec` prints a fixed `/- removed value
     specification -/` and drops its skips; the Coq backend has the same
     pattern.
   - on record fields;
   - between match arms;
   - after an expression or a match arm.
2. **Backend comments not flagged.** The backend writes 26 `/- Arc-10 S2: … -/`
   blocks into linksem's generated tree, 25 blocks on OCaml
   polymorphic-compare constructor rank, 11 "Backend-derived computable
   structural size" blocks, and `removed …` markers. None of them is marked
   as backend text, and some use internal jargon.
3. **Blank lines between constructors.** The separator printer
   `sep x s = ws s ^ x` prints the source whitespace before each `|`
   (`"\n  "`). The backend then adds its own `"\n"` and `"  | "`. The
   skips hold the comments as well as the whitespace, so S1 fixes this
   finding and finding 1 with one mechanism.
4. **Mutual and recursive records become single-constructor inductives.**
   The reason given at `src/lean_backend.ml` `Te_record` is "Lean 4 mutual
   blocks cannot contain structure definitions". On Lean 4.32.2 that is
   false. A mutual block of two `structure`s, recursive through `Option` and
   `List`, elaborates; `{ s with … }` works; `SSub.rec` is the expected
   nested recursor. So the inductive form is not forced. Consumer exposure:
   - Cerberus's hand-written `CabsImport.lean:661` builds `specifiers.mk …`
     positionally. That also works with a `structure`.
   - The generated accessor names are the names Lean gives structure
     projections.
   - The affected types are Cerberus `statement`/`specifiers` and linksem
     `sdt_subroutine`/`sdt_lexical_block`.
5. **Memory.** `Dwarf.lean` is the largest generated module (5,773 lines).
   It elaborates in 6.3 s with a maximum resident set of 816,284 kB under a
   16G cgroup cap (`/usr/bin/time -v`).
   - The 20 GB failure was an address-space limit. Lean reserves address
     space per thread, so such a limit kills it while its resident memory is
     small; `scripts/capped` documents the same trap.
   - The memory use is not suspicious.

## 3. Rulings

- [USER 2026-10-03] Ordering against the failure-monad translation (TODO 24,
  the side-effect-free output Cerberus asked for): niceness first. S1–S3
  land first under a text-only gate. The failure-monad design pass then
  works on readable output.
- [USER 2026-10-03] Tray scope: all 16, re-verified. Every upstream-Lem
  finding recorded in the Cerberus, linksem and lem-lean docs gets a draft.
  This includes the five that are only on the archive branch
  `archive/linksem-fixes-2026-09-30` and the machine-word findings. Each
  draft's reproducer is run against pristine upstream `3802cb0`. Filing
  stays with the operator.
- [USER 2026-10-03] Tray home: lem-lean, with the existing copies staying. The new tray is
  `doc/upstream-tray/` in lem-lean. The existing Cerberus
  `upstream-tray/lem/01` and linksem `upstream-tray/lem/01` drafts are left
  untouched, so no consumer-repo changes are needed.

## 4. Slices

One coherent commit per slice; every merge into `mdd/lean-backend` is asked
for separately.

| Slice | Content | Gate |
|---|---|---|
| S1 comments + layout | Carry over every source comment (removed `val`/`declare`, record fields, match arms, trailing comments). Fix the constructor blank lines. Give every backend-written comment one recognisable marker and remove the internal jargon. | Comprehensive suite. Non-Lean output byte-identical. The Lean declaration census of Cerberus and linksem unchanged before/after (Cerberus plan P2c-5's exit test). A new comment-coverage check, plant-tested. |
| S2 records | Mutual and recursive records become `structure`s. Stop needless field renames: `forest : list forest` emits `forest0`. | Comprehensive suite. Both consumers build. The Cerberus ladder and the linksem corpus differential. |
| S3 general niceness | Cerberus plan P2c-5 (width-bounded printer, `.lem` line references) and P1d-9 (double spaces, `(({…} : T))`, …). Starts with a written review of the output, whose item list the operator scopes before any code. | As S1. |
| S4 docs + TODO | README and DESIGN describe the backend as it is; history moves to records; TODO.md becomes one clean register. | Review. |
| S5 lem tray | `doc/upstream-tray/` in the Cerberus format (README, INDEX, one draft per finding, verbatim reproducer output). `upstream-pr/*` branches only where a fix exists. | Verbatim outputs. |

Landing: linksem re-pins after each lem merge. The Cerberus re-pin waits for
the lem-pin slot, which the Cerberus next-phase plan §11.5 shares with the SC
track: one pin dance at a time.

## 5. Constraints from the Cerberus worker (relayed by the operator, 2026-10-03)

Relayed verbatim in substance (the operator's message quoting the Cerberus
worker):

- The shared switch and `deps/lem-pinned` stay at `77ad4fa` until the
  Cerberus `_Alignas` and union-twin slices have landed. Those slices
  regenerate Cerberus's trees, and a lem change in the middle of a slice
  would shift the generated code underneath their gates.
- Every lem-side slice runs `make upstream-drift`, which compares the fork's
  non-Lean output against pristine upstream Lem. Keeping it at "no code
  differences, Cerberus's and linksem's OCaml byte-identical" guarantees
  that lem changes do not move Cerberus's oracle.
- The lem mainline already leads the Cerberus pin (the drift harness, the
  Coq rename). This arc adds to that lead, and the next Cerberus re-pin
  picks it all up at once, after both bug fixes land, unless one of this
  arc's changes affects Cerberus sooner.

How this arc complies [AGENT]:
- Every generation uses the worktree's own in-tree `lem`, writing into
  scratch directories. Verified 2026-10-03: `deps/lem-pinned` is at
  `77ad4fa`, and the switch's `lem -v` prints
  `Lem lean-backend-v0.1.0-alpha.1-20-g77ad4fa`.
- The drift check is part of each slice gate. It runs against pristine
  clients: `deps/cerberus-upstream` and linksem's `worktrees/linksem-upstream`.

## 6. Corrections and findings during the arc [AGENT]

- **Tray count.** When the operator was offered the tray scope, the
  orchestrator said "16" findings, five of them archive-only. That was a
  miscount: the surveyed inventory was 15 mainline items, the `§` lexer
  defect and the five archive-only findings. The tray worker also found the
  `output.ml` block-format decode to be a genuine upstream bug, and the
  orchestrator found the comments-before-`and` loss. The tray therefore
  holds 23 drafts, and its INDEX.md carries the arithmetic. The ruling's
  intent was all of them, re-verified; the number put to the operator was wrong.
- **Comments before `and` in recursive function groups (not fixed in S1).**
  The Lean pipeline loses them, as upstream's prover backends do (tray
  draft 23, reproduced on pristine `3802cb0`):
  - Upstream's `Patterns.remove_toplevel_match` regroups the clauses and
    rebuilds the separators. In Cerberus's `cabs_to_ail.lem` the 18 distinct
    separators of one group became 2.
  - An attempt to print the separators' comments therefore printed one
    comment in front of 29 different definitions. It was reverted, failing
    closed: a missing comment, not a misplaced one.
  - A fix in the shared `patterns.ml` would move Coq/HOL/Isabelle output,
    which the drift guarantee above forbids. It is an upstream report; any
    Lean-only fix needs its own decision.

## 7. S1 record: comments and layout (2026-10-03)

**Changes** (`src/lean_backend.ml`; `src/process_file.ml`, Lean branch only):
- Source comments are kept at every position the backend lays out:
  - a removed `val` (its comments in front, then those inside its type);
  - every `declare`;
  - constructors (trailing comments on the line, leading ones on their own
    lines);
  - record fields and the closing `|>`;
  - `and` in type groups;
  - match arms;
  - the leading comments of every expression, which are taken out of its
    skips in `exp`, so no rendering path can drop them.
- Each source comment is emitted once per file. The identity is physical:
  pattern compilation copies a skip list into several arms.
- A comment inside a one-line expression has its line breaks folded to
  spaces. Lean's layout is column-sensitive, and the census build caught a
  `|` arm ended early by a multi-line comment (`Dwarf.lean`).
- Comment text is escaped (`-/`, `/-`) and padded, so it can neither end
  the Lean comment early nor form `/--` or `/-!`.
- Every comment the backend writes starts with `lem: `. The internal
  jargon is gone. The fixed `removed value specification` marker is gone,
  because a `val` has no Lean counterpart.
- `normalize_layout`, applied to every generated file: outside strings and
  comments, it removes trailing spaces and makes each run of blank lines a
  single blank line. That fixes the blank, indented line between
  constructors.
- New gate `lean-comments`: `tests/comprehensive/test_comments.lem` and
  `check_comments.py`. It checks:
  - every comment is present exactly once; the registered loss is tagged
    `KNOWN-LOST` and must stay absent;
  - no code follows a multi-line comment on its last line;
  - no whitespace-only lines and no blank-line runs.

  Plant-tested 2026-10-03 against copies of the generated file: a removed
  comment gives C1, a duplicated one C2, a multi-line inline comment C3,
  a blank-line run C4, and an emitted `KNOWN-LOST` comment C1.

**Measurements** (scratch tools, derived numbers):

| Tree | Missing comments before → after | Duplicated before → after | Code after a multi-line comment before → after |
|---|---|---|---|
| Cerberus (85 `.lem`) | 958/4060 → 64/4060 | 1 → 0 | 7 → 0 |
| linksem (96 `.lem`) | 927/3833 → 47/3833 | 2 → 2 (both pre-existing) | 6 → 0 |

Both generated trees and LemLib's checked-in sources (30 files) are
token-identical to `6e2526e`'s output, modulo comments and whitespace. The
token check normalises whitespace next to brackets. It was plant-tested on
a `Nat`→`Int` change and on a split `:=`.

**Declaration census** (`Census.lean`: every constant of every generated
and hand-written module; name, kind, structural hashes of type and value):
- **linksem:** 11782 constants in 193 modules, before and after identical
  (0 diff lines). Plant: one string literal changed in `Dwarf.lean` moved
  `attribute_encodings`' value hash. After the revert and a rebuild, 0
  diff lines again.
- **Cerberus** (219 modules, built against the LemLib pin `77ad4fa`):
  - The strict census differs in `Cabs` only, in 360 lines. They are
    hygienic auxiliary names of derived instances
    (`…match_on_same_ctor._@.Cabs.…._hyg.N`), plus the values of 120
    `beq_N`/`ord_N` internals that reference them. Their types are
    unchanged.
  - With macro scopes erased from every constant name (`--erase-scopes`),
    before and after are identical: 34229 constants, 0 diff lines.
  - The strict census is deterministic: a second run on the same build
    gives 0 diff lines.
  - Finding: S1 renumbers inaccessible hygienic helpers in `Cabs`. No
    accessible declaration changes.

**Gate on the candidate** (verbatim tails):
```
make exit 0
lemlib exit 0
Build completed successfully (39 jobs).
comprehensive exit 0
=== Generation: 68 passed, 0 failed, 0 skipped ===
=== Comments and layout (gate) ===
  OK: Test_comments.lean: comments preserved, layout sound
Build completed successfully (197 jobs).
parity: 48 probes: 38 OK, 10 XFAIL (registered, Lean side pinned), 0 FAIL
  OK: 308 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
upstream-drift: 944 upstream files; 198 differ (list: …/drift3/differences.txt)
library code files (OCaml/HOL/Isabelle/Coq):
  comments/whitespace only  lib/coq/lem_basic_classes_auxiliary.v   [… 32 such rows, no code row]
lean_keyword_probe: 178 core keywords checked
```
Drift notes:
- The pristine clients were `deps/cerberus-upstream` (`b9aeedcb4`) and
  linksem `worktrees/linksem-upstream` (`4464128`).
- `cerberus-ocaml` and `linksem-ocaml` are absent from the differences:
  their output is byte-identical.
- The non-zero exit is the script reporting the fork's known non-code
  library differences (tex/html/lem renderings), the classes accepted when
  the drift check landed (`98b83c5`).
- S1 changes no shared code. The diff is in `lean_backend.ml` and in
  `process_file.ml`'s Lean branch.

**Not fixed in S1:**
- Comments before `and` in recursive function groups (TODO 26).
- The mutual-record comments of `sdt_subroutine`, which are S2's: the
  records move to the fixed `structure` path.
- Cosmetics, which are S3's: double spaces (`|  Red`, `def  f  (x`), a
  leading space on some own-line comments, the blank line after a
  structure's last comment.
- Lem theorems are emitted as `/- lem: theorem NAME not translated -/`.
  The statement is not kept, although the backend README says theorems are
  "emitted as comments". The S3 review settles this.

## 8. S2 record: mutual records as structures (2026-10-03)

**Change** (`src/lean_backend.ml`):
- A record in a mutual block whose members all have the same number of
  type parameters is now a Lean `structure`. Records in other mutual
  blocks are unchanged. Its fields are printed by S1's field printer, so
  field comments are kept.
- Lean generates the field projections. The hand-made accessor `def`s,
  `match self with | .mk _ _ x .. => x`, are gone. The projections have
  the same names.
- Literals, updates and supply threading of these records take the
  ordinary record path, i.e. `{ f := v, … }` and `{ r with f := v }`.
  Before, a literal was a positional `T.mk` and an update was a positional
  `T.mk` restating `(r.field)` for every unchanged field.
- `St.mutual_records`, and with it `mutual_record_path`, now lists only
  records in a block whose members have different numbers of type
  parameters. Such a block is emitted with indices (`type_def_indexed`,
  `Type 1`). A Lean structure cannot have indices, so there the
  single-constructor inductive is forced and keeps its positional B7
  emission.
- The S1 field printer dropped the comments between `=` and `<|`: the
  first field's handling overwrote them. Both record paths now keep them.
  The case is added to `test_comments.lem`.

**Lean facts checked on 4.32.2** (scratch `mix.lean`, `fld.lean`, run 2026-10-03):
- An `inductive` and a `structure` may share a `mutual` block.
- Structural recursion over `.mk` patterns works through `List`/`Option`
  nesting.
- A recursive parametric structure is accepted.
- `{ b with name := "x" }` elaborates to
  `{ name := "x", body := b.body, parent := b.parent }`.

**Withdrawn [AGENT]: "stop needless field renames"** (§4, the S2 row). The
rename is not needless. In a structure, a field's name is in scope in the
types of the later fields, so a field named like a type captures them.
`structure tree where forest : List forest; other : forest` fails with
`type expected, got (forest : List _root_.forest)`. Lem's renaming of
such fields (`forest` → `forest0`) is what keeps the generated structure
well-formed.

**Gate on the S2 candidate** (FAST-GATE: the commit-level gate of the
two-tier rule; the behavioural lanes run at the merge):
- comprehensive suite: `=== Generation: 68 passed, 0 failed, 0 skipped ===`,
  `OK: Test_comments.lean: comments preserved, layout sound`,
  `Build completed successfully (197 jobs).`,
  `parity: 48 probes: 38 OK, 10 XFAIL (registered, Lean side pinned), 0 FAIL`.
  `test_mutual_record_order.lem` now also covers a heterogeneous block;
  its asserts `mro_h_lo`/`mro_h_hi`/`mro_h_upd` print PASS.
- `nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)`.
- Both consumers build: the linksem library, the Cerberus `CerberusLean`
  library against LemLib `77ad4fa`, and the hand-written `CabsImport.lean`
  with its positional `specifiers.mk`.
- **Census against S1** (linksem strict; Cerberus with macro scopes erased):
  - Changes occur only in `Dwarf` (linksem) and in `AilSyntax` and `Cabs`
    (Cerberus).
  - What changed: the accessor `def`s became projections with the same
    names; `T.mk._flat_ctor` is new; the matcher numbering inside
    `lemSize` moved (`T.lemSize.match_1` is new, and
    `T.<first field>.match_1` is gone).
  - What did not change: the types, their constructors and recursors, and
    every definition that builds, reads or updates these records. In
    particular, `AilSyntaxAux`'s text changed (literals in structure
    syntax) while its declarations are identical.
- The last change, the `<|` comments, is comment-only: its output is
  token-identical to the trees the census was built from. The only
  exceptions are Cerberus's `Core_run` `import Operators`, which the
  Makefile strips, and linksem's two stale `Dump_image*` files.
- Comment coverage after S2: Cerberus 62/4060 missing, linksem 42/3833.

## 9. S3 scope (2026-10-03)

**Review.** A fresh reviewer read the generated output as an experienced
Lean user would. Its findings were grouped into four packages. The
orchestrator re-measured the headline numbers:
- 48% (linksem) and 59% (Cerberus) of the generated text sits on lines
  over 200 characters; the longest line is 105,883 characters.
- `Â§` appears in 32 files.
- Cerberus has 1,044 `(priority := 500)` instance headers.

The packages:
- **A, layout engine:** one-line bodies broken into one arm per line at
  the author's indentation; comments that drift past a signature's result
  type.
- **B, printer cleanup:** spacing, parentheses around atoms and doubled
  parentheses, merged `open` lines, merged binders, the garbled `§` in
  comments.
- **C, derived-code compaction:** shorter instance and derived
  boilerplate. It changes declarations.
- **D, names, docs and types:** docstrings, kept abbreviations, fewer
  renamed locals, fewer ascriptions. Consumer-visible.

**Ruling** [USER 2026-10-03], answering "Which packages should the S3
niceness pass include?": A (layout engine) and B (printer cleanup), the
recommended ones. C and D are not in this arc; they stay candidates
for later decisions. Order [AGENT]: B, then A. Gate for both: the
generated declarations are unchanged, as shown by the declaration census
on both consumers; the token check also applies to whitespace-only steps.

## 10. S3-B record: printer cleanup (2026-10-03)

**Changes** (`src/lean_backend.ml`):
- **B1 spacing** (`normalize_layout`). Outside strings, character literals
  and comments: a run of spaces inside a line becomes one space; there is
  no space after `(`/`[` or before `)`/`]`/`,`; `×` has one space on each
  side. Line-start indentation is untouched.
- **B2 parentheses.**
  - Types: a `Typ_paren` around an atom (decided on the printed text, so a
    multi-token target representation keeps its parentheses) or around a
    tuple or another paren is dropped, unless it holds a comment.
  - Expressions (`normalize_layout`): `( atom )` becomes `atom`, for a name
    or a numeral. A space is inserted where tokens would otherwise join. Not
    taken: a numeral followed by `.`, and the name list of an `export` or
    `open` command (it needs its parentheses).
- **B3:** each list of `open`s is one statement, wrapped at about 80
  columns.
- **B4:** adjacent implicit binders of one kind share a binder,
  `{a b : Type}`. Only adjacent ones, so the argument order and the
  declaration types are unchanged. In Cerberus, 530 pairs of adjacent
  separate binders became 10.
- **B5 the garbled `§`.** Lem's lexer reads comment bytes as Latin-1
  (upstream tray draft 02). The Lean output undoes that on each comment
  text fragment, when the result is valid UTF-8. `Â` is gone from both
  trees (32 files before). OCaml output is untouched.

**Gate**:
- **Declaration census** against S2:
  - Cerberus with macro scopes erased: 0 diff lines.
  - linksem with macro scopes erased: 0 diff lines.
  - linksem strict census: 18 lines differ. These are the hygienic helper
    names of `c_type_top`'s derived instances (`_hyg.261` → `_hyg.245`)
    and the two instance bodies that reference them. Removing parentheses
    removes macro expansions during elaboration, which renumbers the
    module's later hygienic names; this is the same phenomenon as in S1.
- **Comprehensive suite:**
  `=== Generation: 68 passed, 0 failed, 0 skipped ===`,
  `OK: Test_comments.lean: comments preserved, layout sound`,
  `Build completed successfully (197 jobs).`,
  `parity: 48 probes: 38 OK, 10 XFAIL (registered, Lean side pinned), 0 FAIL`.
- `nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)`.
- Comment coverage is unchanged (62/4060, 42/3833), with no layout
  hazards.

**Caught by the gate and fixed before this commit:**
- `export Show (show0)` → `export Show show0`, which is invalid.
- `Show (a × b)` → `Show(a × b)`: the removed paren's leading whitespace
  was dropped.

The first census run failed to build both consumers on these two bugs.

**Process note:** linksem's primary checkout moved during the arc, to
`3699e83`, by another agent. From this slice on, the scratch generators
read a frozen copy of linksem's sources (the arc's starting sources) and a
detached Cerberus worktree at `f3d9cc419`
(`worktrees/cerberus-lean-frozen-niceness`; its `.lem` files are identical
to `621caf996`'s).

## 11. S3-A record: layout engine (2026-10-03)

Branch `arc/output-niceness-layout`, from `arc/output-niceness` at `2e54ff0`.
Package A of §9: the generated Lean reads like the source. Text-only; the
declaration census is the exit test (Cerberus plan P2c-5).

**Design** [AGENT]: a token-stream formatter over the final text,
`src/lean_layout.ml`, run by `normalize_layout` after the spacing pass of
S3-B (now `normalize_spacing`). Not the `Output` block machinery: enabling
it would mean revisiting every emission site of the backend and arguing
about OCaml `Format`'s box breaking against Lean's column rules; one pass
over the text, with the lexer conventions of `normalize_spacing`, keeps the
layout decision in one place and makes fail-closed trivial.

- **Units.** A declaration (`def`, `theorem`, `abbrev`, `instance … :=`,
  with attributes and modifiers) and all its lines up to the next item is
  re-laid out from its tokens at indentation 0; a blank or comment-only
  line is part of the body when a bracket is still open or the next code
  line is a continuation. A header ending in `where`, each item of an
  `instance`/`structure`/`inductive` body (with the lines that close its
  brackets) and each `export` line is laid out on its own at its own
  indentation. Imports, opens, comments, `deriving`, `termination_by` and
  the like are copied.
- **Structure recovered:** brackets; `match … with | … => …` (also with
  several discriminants); `fun … => …`; `let … := …; …`; `if`/`lem_if …
  then … else …` (an `else if` chain stays flat); `{ … }` instances and
  `{ r with … }` updates. Everything else is an application sequence.
- **Printer:** Wadler/Leijen groups (flat if the group fits, else its
  breaks are taken); application arguments fill the line; match
  alternatives and let bodies are hard breaks (always one per line, as in
  the source); `fun`, `if` and `{ … }` break only when they do not fit. A
  trailing `(fun … =>` argument hugs the line when everything before it
  and its head fit (`Union`), so a chain of monadic binds costs two columns
  per level. The fields of a structure instance, a `let` and a `match` are
  indented relative to their own first field or keyword (`Align`).
- **Width 100** [AGENT]: the Lean community's line length. Lines that hold
  a string literal or a comment wider than that are left wide; neither is
  broken.
- **Token-preserving by construction.** A break is only ever placed where
  the input had whitespace (and after `,`/`;`, delimiter tokens); where
  the input had none (`x=>`, `:=lemNatDiv`, `).f`), none is added.
- **Comments.** A comment that followed a line break in the source (the
  backend now marks it with an `Output.new_line` in `inline_comments`), or
  that spans lines, goes on lines of its own; any other comment trails the
  previous token when a closer or separator follows it, else leads the
  next one; a comment in front of a `let` or `match` always gets a line of
  its own. Multi-line comments inside expressions are no longer folded
  (`inline_comments`; `flatten_newlines` is now
  `Output.flatten_newlines_keep_comments`, an added function in the shared
  `output.ml` with no other caller): the pass puts a line break after
  them, and where it leaves a declaration as it was, it folds them and
  re-joins the backend's marker break, so such a declaration is exactly
  the text that built before.
- **Fail closed.** A declaration the parser does not fully understand (an
  unknown keyword, an unbalanced bracket, a `let` without `;`, a `,`
  outside brackets) is emitted as it was. `LEM_LEAN_LAYOUT_DEBUG=1` lists
  them on stderr.

**Lean 4.32.2 facts relied on** (scratch `.tmp/layout/lay3.lean`,
`lay4.lean`, run 2026-10-03; re-verifying the orchestrator's four):
- an alternative's right-hand side left of its `|` is refused: `expected
  alternative right-hand-side to start in a column greater than or equal to
  the corresponding '|'`;
- a `let` value's continuation line at or left of the `let` column is
  refused (`unexpected token ';'; expected command`), both for a `let` at
  the start of its line and for one in the middle of an alternative;
- a continuation line at column 0 after a top-level body is not an
  argument (`unexpected identifier; expected command`);
- the 42 shapes the pass emits elaborate: alternatives one per line with
  the right-hand side on the next line at +2; a multi-line comment on its
  own lines between alternatives, after `with`, inside an application and
  after `then`; a nested unparenthesised match in a last alternative; a
  parenthesised match as an argument with its alternatives right of the
  bracket line; a lambda body on the next line followed by another
  argument; equations; theorem binders at +4 with the statement on its own
  line; an `export` list wrapped; operators at line ends and line starts;
  a discriminant broken after its comma; an ascription split at `:`; a
  prefix `-` split from its operand; a let value on its own line; a
  structure update and a structure instance broken one field per line,
  aligned under the first field after `((({`; a comment on its own line
  in front of a `let` inside parentheses; `else if` chains; lambda
  binders split across lines; the `lemSeq (fun _ =>\n …)\n (fun _ =>\n …)`
  shape; a lambda with a match body as an argument on its own line.

**Not laid out on purpose.** The four `indreln` constructors
`incReflexive`, `incStep`, `monReflexive`, `monStep` of Cerberus's
`Cmm_op.lean` (`| incStep : ∀ pre x y z a, (` — a `,` outside brackets);
they stay on their lines as before. Comment text and string literals are
never broken.

**Measurements** (derived; `.tmp/layout/linelen.py` over the regenerated
trees: S3-B's output `ref-b` against this slice's `cur`; the §9 headline
numbers were taken before S3-B and on bytes, these are on characters):

| Tree | lines | > 100 | > 200 | > 1000 | longest line | text on lines > 200 |
|---|---|---|---|---|---|---|
| Cerberus before | 32,449 | 4,316 | 1,572 | 317 | 78,812 (`GenTyping.lean`) | 55% |
| Cerberus after | 83,781 | 1,173 | 72 | 0 | 602 (`Formatted_auxiliary.lean`) | 1% |
| linksem before | 26,750 | 3,083 | 1,036 | 158 | 57,266 (`Linker_script.lean`) | 43% |
| linksem after | 51,672 | 1,415 | 30 | 0 | 394 (`Dwarf.lean`) | 0% |

Every line still over 200 columns holds comment text (67 of Cerberus's
72, 17 of linksem's 30) or a string literal (5 and 13); none is code. The
longest line is a backend-written `/- lem: fuel_measure obligation … -/`
comment.

**Gates on the committed source** (verbatim tails).

Gate 1, `check.sh` (regeneration of both trees with the worktree's lem,
`tokdiff` against S3-B's `ref-b`, comment coverage, duplicates, `mlcheck`):
```
[cerb]
tokdiff: identical modulo comments/whitespace (170 files)
[linksem]
tokdiff: identical modulo comments/whitespace (194 files)
comment coverage: 62 of 4060 source comments missing (16 modules)
comment coverage: 42 of 3833 source comments missing (11 modules)
[cerb dup]
duplicated comments: 0
[linksem dup]
duplicated comments: 2
[cerb layout]
code after a multi-line comment: 0
[linksem layout]
code after a multi-line comment: 0
check exit 0
```
`tokdiff.py` [AGENT]: its whitespace normalisation, which already ignored
whitespace next to brackets, commas and `×`, now also ignores it next to
`;` (the pass glues a let's `;` to the value; `;` is a delimiter token).
Plant on `Core_aux.lean` line 584: the `;` of `let backend :=
CerbGlobal.backend_name ();` removed → `tokdiff: DIFFERENT`; the same `;`
given a space on each side → `identical modulo comments/whitespace`.

Gate 2, `census-run.sh a4` (both consumers built from the regenerated
trees — linksem's library and `main_link`, Cerberus's `CerberusLean`
against LemLib `77ad4fa` — then `Census.lean --erase-scopes` diffed against
S3-B's reference censuses):
```
linksem build exit 0
linksem census exit 0
linksem census (erased) diff lines vs B: 0
cerberus build exit 0
cerberus census exit 0
cerberus census (erased) diff lines vs B: 0
```
(build log tails: `Build completed successfully (241 jobs).` and
`Build completed successfully (252 jobs).`; no `error:` line in either.)
The two earlier census runs on intermediate binaries failed to build and
are listed under "found and fixed" below; this is the run on the committed
source.

Gate 3, `make -C tests/comprehensive lean` (the full suite; a first run was
invalidated by this worker rebuilding `lem` underneath it — `../../lem:
not found` in `lean-generate` — and repeated with the worktree untouched):
```
=== Generation: 69 passed, 0 failed, 0 skipped ===
  OK: Test_comments.lean: comments preserved, layout sound
  OK: Test_layout.lean: layout sound (15 alternatives, 2 lets, 14 comments, width 100)
Build completed successfully (199 jobs).
parity: 48 probes: 38 OK, 10 XFAIL (registered, Lean side pinned), 0 FAIL
  OK: 11 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
  OK: 311 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
comprehensive exit 0
```
LemLib, regenerated by `make` (27 of its 30 checked-in sources change,
layout only) and built with `scripts/capped lake build` in `lean-lib/`:
```
Build completed successfully (39 jobs).
lemlib build exit 0
```
The `assert`s lem emits as `#eval do …` blocks are left as they were: `do`
is not a construct the pass lays out (fail closed, by design).

`nonlean-regress`:
```
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
```
`upstream-drift` was not run in this slice: it needs a built pristine
upstream Lem checkout, which no longer exists in the container and which
this worker may not create (a worktree of the primary repo). The slice's
only change to shared code is the added `Output.flatten_newlines_keep_comments`,
called from the Lean backend alone; `nonlean-regress` holds the fork's
non-Lean output byte-identical. The drift check is left to the orchestrator
at the merge.

**New gate `lean-layout`** (`tests/comprehensive/test_layout.lem`,
`check_layout.py`, rule in the `lean` target, roots in the lean-test
lakefile): long nested matches, a nested match with a long first
alternative, a bind chain, lets, an if-chain, a record literal, a list
with a comment on every element, a long header, comments in every
position. Rules: L1 every `|` is the first token of its line; L2 a let's
`;` is the last code token of its line; L3 a line without a string or
comment is at most 100 columns; L4 no code after a multi-line comment on
its last line; L5 vacuity (the file must hold an alternative, a `let` and
a comment).
```
  OK: Test_layout.lean: layout sound (15 alternatives, 2 lets, 14 comments, width 100)
```
Plants (modified copies of the generated file, 2026-10-03):
```
  FAIL: L1 …/p1_arm_joined.lean:76: `|` is not the first token of its line: '(String.append " in " cfg.cfg_name)) /- leading an alternati'
  FAIL: L2 …/p2_let_body_joined.lean:104: code after the `;` of a let: '(let n := List.length sides; /- between two lets -/ let tota'
  FAIL: L3 …/p3_wide_line.lean:69: 118 columns, no string or comment to excuse it
  FAIL: L4 …/p4_code_after_comment.lean:93: code after a multi-line comment: 'lem_if'
  FAIL: L5 …/p5_vacuous.lean: vacuous — alternatives=0 lets=1 comments=1
```
(each plant exits 1; the clean file exits 0.)

**Found and fixed on the way** (each caught by a gate, none reached a
commit): the hug layout printed a lambda's stored head and lost a comment
attached in front of it (`(/- 1-byte delta -/ fun …`, linksem `Dwarf`);
the header's result-type split dropped a comment attached to the `:`
(`(bs0 : T) /- os proc usr hdr sht stbl -/ : String`, four linksem
harness functions); the hug's fit check could stop at a hard break inside
the first argument; the first census run failed both builds on structure
fields not aligned with the first (`((({ name := …,`) and on a `let`
pushed off its line start by a comment, and the second on a `let` in the
middle of a line (`match let i := …` as a discriminant, `(let lo1 :=` in
`Cmm_csem`) — the `Align` rule above is the fix; `x=>` and `:=lemNatDiv`
(no space, left by S3-B) were one token to the first lexer, and the fixed
keyword spacing of the first printer added a space there.

## 12. Arc close: integration and final gate (2026-10-03)

**Integration.** The branches were folded into `arc/output-niceness`:
- `arc/output-niceness-layout` (S3-A, `ac5565b`): fast-forward.
- `docs/lem-docs-rationalize` (S4): rebased onto it, then fast-forwarded:
  - `8dd6ab8`: the docs rationalization;
  - `14d77b5`: the fixes from a fresh reviewer's "accept with fixes"
    review (no MAJOR findings; 33 of 34 checked claims held).
- `74858d9`: the last two backend comments get `lem:`; DESIGN describes the
  layout pass; TODO 42 is closed.

The orchestrator re-verified the S3-A worker's gates independently. The
worker had reported that the drift check could not run, because a pristine
upstream build was missing. The build exists at
`linksem-lean/deps/lem-upstream`, and the orchestrator ran the check.

**Final gate on `74858d9`** (verbatim tails):
```
tokdiff: identical modulo comments/whitespace (170 files)     [vs S3-A output]
tokdiff: identical modulo comments/whitespace (194 files)
comment coverage: 62 of 4060 source comments missing (16 modules)
comment coverage: 42 of 3833 source comments missing (11 modules)
duplicated comments: 0 / 2
code after a multi-line comment: 0 / 0
linksem build exit 0 / linksem census (erased) diff lines vs B: 0
cerberus build exit 0 / cerberus census (erased) diff lines vs B: 0
lemlib exit 0
=== Generation: 69 passed, 0 failed, 0 skipped ===
  OK: Test_comments.lean: comments preserved, layout sound
  OK: Test_layout.lean: layout sound (15 alternatives, 2 lets, 14 comments, width 100)
Build completed successfully (199 jobs).
parity: 48 probes: 38 OK, 10 XFAIL (registered, Lean side pinned), 0 FAIL
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
upstream-drift: 944 upstream files; 198 differ   [32 library code files, all comments/whitespace only; cerberus-ocaml and linksem-ocaml absent: byte-identical]
lean_keyword_probe: 178 core keywords checked
```
- Line lengths, derived:
  - Cerberus: longest line 78,812 → 602 characters; text on lines over
    200 characters 55% → 1%.
  - linksem: longest line 57,266 → 394; 43% → 0%.
  - Lines over 1000 characters: 0 in both trees.
- Behavioural lanes not run: the Cerberus ladder and the linksem corpus
  differential. The declaration census, unchanged since S2 (macro scopes
  erased), is the argument that no behaviour moved. Only S2 changed
  declarations, and only from accessor `def`s to projections with the
  same names.
- **For the auditor:** the erased census is weaker than the strict one.
  Two hygienic helpers can erase to the same name, so a value that switched
  between them would not register. The strict censuses were checked by
  hand for S1 (Cerberus `Cabs`) and for S3-B (linksem `c_type_top`): only
  helper numbers moved, together with the values that cite them.

**Side finding (linksem, not this arc):** `dwarf.lem:5143` writes
`| None ->`. Lem's constructor is `Nothing`, so `None` is a variable
pattern there. It is the last arm and behaves as a wildcard, on OCaml as
well. It is a candidate for linksem's upstream tray.

## 13. Audit fixes (2026-10-03)

The pre-merge audit of the arc at `c423e5c` (a fresh reviewer; notes,
probes and driver in the orchestrator's `.tmp/audit/`) ruled "merge after
fixes". The orchestrator reproduced MAJOR-1, MAJOR-2 and MINOR-2. Fixes
on `arc/output-niceness-layout`, fast-forwarded to `c423e5c` first: the
code, tests and regenerated LemLib in `131b922`, the documents (this
section, DESIGN's layout claims, the three banners, TODO's line
references, RECORDS) in the commit after it; the same gates as §11, all
run on `131b922`'s tree. One finding per paragraph, with its evidence.

Also found by the new test and fixed in `131b922`: the auto-import rule
for dotted `target_rep` text (`collect_cr_simple_import`) accepted any
prefix whose first byte is its own upper case, so `(fun (p : Nat × Nat)
=> (p).1)` produced `import (fun (p : Nat × Nat) => p` and the module
did not build. It now accepts only an identifier-shaped module name. No
consumer text changes (such a rep would already have broken its build).

**MAJOR-1 — `normalize_spacing` split tokens.** `(x).1` became `x .1`
(the atom rule put a space before a following `.`), `'×'` became `' × '`
(a character literal with a multi-byte character was not recognised, so
the `×` rule spaced it) and `×'` became `× '` (the `×` rule did not know
the `PProd` token). All three are reachable through `declare lean
target_rep` text and Lean rejects them. Fixes in `src/lean_backend.ml`:
a `char_literal_end` that accepts an escape or one UTF-8 character of one
to four bytes; `×` followed by `'` is copied; a `.` after a removed atom
stays attached; `«…»` names are copied as they are (a space inside is
part of the name). Evidence (the auditor's `drv/t_spacing.lean`, run
through the current spacing pass with a driver built from the worktree,
`.tmp/layout/lay-driver2`; `<` after, `>` before):
```
< def a2 (x : Nat × Nat) := x.1
> def a2 (x : Nat × Nat) := x .1
< def a5 : Char := '×'
< def a6 : Type := (_ : Nat) ×' Nat
> def a5 : Char := ' × '
> def a6 : Type := (_ : Nat) × ' Nat
<   open Foo (bar)
<   export Foo (bar)
>   open Foo bar
>   export Foo bar
```
Lean 4.32.2 on the two outputs: before, `5:20: error: missing end of
character literal`, `2:26: error: Function expected at` (the `.1`) and
`25:12: error: unexpected identifier; expected '('` (the indented
`export`); after, none of the three (the probe's other errors are its
undefined names, the same on both sides).

**MAJOR-2 — the renderer altered token text.** `render` right-stripped
and dropped empty lines over its whole buffer, so a multi-line string
literal lost a blank line and trailing spaces (a value change) and a
multi-line comment inside a laid-out body lost its blank lines; the lexer
split `«a b»` at the space and the fill broke it over two lines. Fixes in
`src/lean_layout.ml`: the renderer builds its lines between its own
breaks and trims only those (a token never ends in a space; a line of
nothing but indentation is dropped), a token holding line breaks is
copied as it is and never fits a line (`MLText`, as comments already
were), and `«…»` is one token. Evidence (the auditor's
`drv/t_layout.lean` through the full pass, `cat -A`):
```
  "line one$
  line two$
$
line four with trailing spaces   $
end" ++ "and a long tail to push it over the width limit of one hundred columns for sure yes yes"$
```
and `«a b»` is kept whole at the line break (`… + «a b» +$` / `    «a b»$`).
In the consumers this restores the blank and whitespace-only lines inside
multi-line comments that the previous renderer had removed (see "what
changed" below); Lean 4.32.2 accepts the whole `t_layout` output except
the probe's own `/- a comment-led line -/ IO.println r` inside a `do`
block, which is invalid Lean on any layout (the item starts at the
comment's end column, so it continues the previous item; the error is
the same on the text before the pass).

**MINOR-1 — the fail-closed path was not "as it was".** Commands outside
the keyword lists (`#eval`, `#check`) were swallowed into the previous
declaration, and `verbatim_lines` re-spaced tokens, folded every
multi-line comment that shared a line with code and joined every
comment-led line to its predecessor (inside a swallowed `#eval do` block
this joined `let r := b1 1` and `/- c -/ IO.println r`). Now a line
starting with `#` is a unit boundary and it and the indented lines of its
block are copied; a declaration left as it was is each line's original
text, byte for byte, with exactly two inverses of what the backend does
for the pass: a multi-line comment followed by another token on its line
is folded (the backend no longer folds the comments inside expressions),
and a column-0 line starting with a comment followed by code — the
`Output.new_line` marker `inline_comments` writes before a comment that
followed a line break in the source — is joined to the line before it.
Without these two a left-as-is declaration would not be the text that
built before the pass (a multi-line comment ahead of `| arm`, or the
marker's line break, would end a match early). Evidence: in the
`t_layout` output `#check b3`, `#eval b7 2` and `#eval b8 2` start their
own lines at column 0 and the `#eval do` block's two lines are unchanged.
DESIGN's "left exactly as it was" now says this.

**MINOR-2 — `lean-lib/LemLib/Set.lean` stale at `c423e5c`.** `make`
regenerates it (five `lem:` markers), and with this slice's text changes
also `Basic_classes.lean` and `List.lean` (nested comments, one `(i : Nat)`).
A second `make` changes nothing further. All three are committed.

**MINOR-3 — `check_comments.py` C1 used a substring oracle.** The
auditor's plant `c1_substring2.lean` (the comment `leading a field`
removed, its text embedded in another comment) passed. C1 and C2 now count
exact normalised-text matches over every comment of the generated file,
nested comments counted on their own (a Lem comment nested in a comment is
now a nested Lean comment, and the backend's `lem: replaced by its target
representation` blocks quote source comments inside them). C4 ignores the
lines inside a multi-line comment: they are the author's text, which the
renderer now keeps. Plants (the auditor's set, 2026-10-03):
```
Test_comments      OK: Test_comments.lean: comments preserved, layout sound
c1_substring2      FAIL: C1 test_comments.lem:23: comment missing: 'trailing a field'
c1_substring       FAIL: C1 test_comments.lem:23: comment missing: 'trailing a field'
c1_removed         FAIL: C1 test_comments.lem:23: comment missing: 'trailing a field'
c1_knownlost       OK: c1_knownlost.lean: comments preserved, layout sound
c1_knownlost2      FAIL: C1 test_comments.lem:46: comment tagged KNOWN-LOST now appears; remove the tag
c2_dup             FAIL: C2 test_comments.lem:24: comment emitted 2 times: 'leading a field'
c3_code_after      FAIL: C3 c3_code_after.lean:111: code after a multi-line comment: '| Green => 2 /- trailing an arm -/'
c4_blank_run       FAIL: C4 c4_blank_run.lean:106: two consecutive blank lines
```
(`c1_knownlost` is the plant where the registered loss is absent, which is
the required state.) On `Cabs_to_ail.lean` the three whitespace-only lines
all lie inside comments and C4 reports none.

**NITs taken.** Nested Lem comments: only the author's text is escaped
(`escape_lean_comment_text`), a nested comment keeps real delimiters (with
a space before `/-` when the text before it ends in `-`), so
`/ - a nested / - twice - / comment - /` is now `/- a nested /- twice -/
comment -/`. A lone `:` (not `::`, not `:=`) gets a space on each side:
`(x :(Nat × Nat))` → `(x : (Nat × Nat))`, `(pc :parse_context)` →
`(pc : parse_context)`. `in_export_or_open` skips the line's indentation,
so an indented `open`/`export X (y)` keeps its parentheses (the evidence
block of MAJOR-1). Not taken: NIT-2 of the notes (an expression's leading
own-line comment trails `:=` because `take_comments` drops the whitespace
that carried the line break) — a backend change with its own hazard
surface, left for a slice of its own.

**Regression gate `lean-text-fidelity`** (`tests/comprehensive/test_text_fidelity.lem`,
`check_text_fidelity.py`, the hand-written `lean-test/TestTextFidelityHelper.lean`
for `«a b»`, roots in the lakefile, rule in the `lean` target): `×'` (a
`target_rep` type and function), `(p).1`, `'×'`, `«a b»` and the
`assert`s' `#eval do` blocks, all through `target_rep` text; the module
compiles and its asserts run in `lean-compile`. Rules T1–T6 are
byte-checks on the code (comments and strings blanked), T6 is vacuity. A
multi-line string literal is NOT reachable from Lem: a string literal's
line breaks are emitted as `\n` (the auditor's `p_mlstring.lem` →
`"line one\n  line two\n\nline four with trailing spaces   \nend"`), and
Lem's lexer refuses a line break inside backquoted `target_rep` text
(`Lexical error: unknown character \``, `.tmp/layout/fid/t_ml.lem`); the
renderer's handling of one is covered by the driver evidence above.
```
  OK: Test_text_fidelity.lean Test_text_fidelity_auxiliary.lean: target_rep text intact
```
Plants (mutated copies of the generated modules):
```
t1     FAIL: T1 …/t1_main.lean:26: `× '` found
t2     FAIL: T2 …/t2_main.lean:23: ` .1` found
t3     FAIL: T1 …/t3_main.lean:26: `× '` found
t4     FAIL: T4 …/t4_main.lean:37: `«a b»` broken over a line
t5     FAIL: T5 …/t5_aux.lean:12: `#eval do` block changed: ['  if ((use_fst == …
t5b    FAIL: T5 …/t5b_aux.lean:11: `#eval` not at the start of its line: '#eval
```

**What changed in the consumers' text** (against the `c423e5c` trees,
`.tmp/layout/ref-c`; derived counts from `diff -r`): Cerberus 16 and
linksem 124 lines where a lone `:` gained its space; 436 and 107 lines
where a nested comment's escaped delimiters became real ones; 43 and 74
blank or whitespace-only lines restored inside multi-line comments. No
code token moved: `tokdiff` identical on both trees, with its
normalisation extended to the whitespace next to a lone `:` (and no longer
ignoring the space in `× '`, which is how MAJOR-1's third case had slipped
past it).

**Gates on the committed source** (verbatim tails).

Gate 1, `check.sh` against `ref-c` (the `c423e5c` trees):
```
[cerb]
tokdiff: identical modulo comments/whitespace (170 files)
[linksem]
tokdiff: identical modulo comments/whitespace (194 files)
comment coverage: 62 of 4060 source comments missing (16 modules)
comment coverage: 42 of 3833 source comments missing (11 modules)
duplicated comments: 0
duplicated comments: 2
code after a multi-line comment: 0
code after a multi-line comment: 0
cur/cerb.log:4
cur/linksem.log:0
```
(the four declarations left as they were are the `indreln` constructors of
§11.)

Gate 2, `census-run.sh f2` (both consumers built from the trees of the
committed binary; erased census against S3-B's references; an earlier
run `f1` on the binary before the auto-import fix gave the same lines):
```
linksem build exit 0
linksem census exit 0
linksem census (erased) diff lines vs B: 0
cerberus build exit 0
cerberus census exit 0
cerberus census (erased) diff lines vs B: 0
```
(build log tails: `Build completed successfully (241 jobs).`,
`Build completed successfully (252 jobs).`)

Gate 3, `make -C tests/comprehensive lean`:
```
=== Generation: 70 passed, 0 failed, 0 skipped ===
  OK: Test_comments.lean: comments preserved, layout sound
  OK: Test_layout.lean: layout sound (15 alternatives, 2 lets, 14 comments, width 100)
  OK: Test_text_fidelity.lean Test_text_fidelity_auxiliary.lean: target_rep text intact
Build completed successfully (202 jobs).
info: Test_text_fidelity_auxiliary.lean:12:0: PASS: fst_of_1
info: Test_text_fidelity_auxiliary.lean:16:0: PASS: ab_is_7
parity: 48 probes: 38 OK, 10 XFAIL (registered, Lean side pinned), 0 FAIL
  OK: 11 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
  OK: 314 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
comprehensive exit 0
```
(a first run of the suite, before the auto-import fix, failed in
`lean-compile` on exactly that bogus `import` line:
`Test_text_fidelity.lean:5:7: expected identifier`.)

LemLib, regenerated by `make` (`Set.lean`, `Basic_classes.lean`,
`List.lean`; a second `make` changes nothing) and built with
`scripts/capped lake build` in `lean-lib/`:
```
Build completed successfully (39 jobs).
lemlib build exit 0
```

`nonlean-regress`:
```
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
```
`upstream-drift`: as in §11, left to the orchestrator (no pristine
upstream Lem in the container; the slice's shared-code change is still
the one added `Output` function).

## 14. Erratum and audit close (2026-10-03, orchestrator)

**Erratum to §8 (S2 census).** §8 says that, apart from the
accessor-to-projection change, the S2 census found "types, constructors,
recursors and every use site" identical. The pre-merge auditor's stricter
census (`.tmp/audit/tools/Census2.lean`) disagrees in two respects:
- It canonicalises hygienic names by the hash of their own definition.
- It also compares definitional heights and flags.

Measured on the before/after builds, it finds the S2 set plus one class
that the §8 census could not see. The definitional height of
`instLocatedStatement` and `mark_as_forloop_body` drops (`h=reg2→reg1`),
because the accessors they unfold are now projections. Neither is a
behaviour change. The §8 statement is corrected by this note; §8 itself is
left as written.

**Audit close.** Fresh Fable audit, asked for by [USER 2026-10-03] over the
full range. Verdict: `arc/output-niceness` merge after fixes;
`docs/lem-upstream-tray` merge.
- The fixes are `131b922` and `0885bf6` (§13), by the S3-A worker.
- The orchestrator reproduced MAJOR-1, MAJOR-2 and MINOR-2 before the fix,
  with the auditor's driver.
- After the fix, the orchestrator re-verified on `0885bf6`:
```
make exit 0   [tree clean after make]
tokdiff: identical modulo comments/whitespace (170 files) / (194 files)   [vs c423e5c output]
comment coverage: 62 of 4060 / 42 of 3833; duplicated 0 / 2; code after a multi-line comment: 0 / 0
linksem census (erased) diff lines vs B: 0 / cerberus census (erased) diff lines vs B: 0   [both builds exit 0]
lemlib exit 0
=== Generation: 70 passed, 0 failed, 0 skipped ===
  OK: Test_comments.lean: comments preserved, layout sound
  OK: Test_layout.lean: layout sound (15 alternatives, 2 lets, 14 comments, width 100)
  OK: Test_text_fidelity.lean Test_text_fidelity_auxiliary.lean: target_rep text intact
Build completed successfully (202 jobs).
parity: 48 probes: 38 OK, 10 XFAIL (registered, Lean side pinned), 0 FAIL
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
upstream-drift: 944 upstream files; 198 differ   [32 library code rows, all comments/whitespace only; cerberus-ocaml / linksem-ocaml absent]
lean_keyword_probe: 178 core keywords checked
```
- The S3-A worker reported twice that the drift check could not run,
  because no pristine upstream Lem existed. The orchestrator found the build
  at `linksem-lean/deps/lem-upstream` (`Lem 3802cb0`) and ran the check.
  The worker's report most likely reflects a sandbox read restriction.
