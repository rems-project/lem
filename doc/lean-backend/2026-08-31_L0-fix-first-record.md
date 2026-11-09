# L0 fix-first slice record — 2026-08-31

Provenance: L0 worker slice of the effect-retirement arc (charter:
cerberus-lean `lean_frontend/docs/2026-08-31_effect-retirement-design.md`
@ 913ee31d1, §8.1 L0; items from
`doc/lean-backend/2026-08-31_backend-quality-review.md`). Branch
`arc/effect-retirement`, base 582d901. All decisions below are [AGENT]
unless marked otherwise; quoted outputs are verbatim; tallies marked
"derived" are derived.

Preliminary ([AGENT]): the quality-review record (commit 0962814 on
sibling branch `review/backend-quality`) was not on this branch though
the charter's §10 cross-reference and the slice brief expect it here;
cherry-picked as e591865 (content unchanged) so the record resolves
in-branch. `e591865` = the pre-slice backend state used below as "old
lem" for red legs and invariance sweeps (scratch build via
`git archive`, deleted at slice end).

## Commits (in order)

| Item | Commit | Disposition |
|---|---|---|
| — | e591865 | review record cherry-pick (docs-only) |
| 1 (M1) | 8abf4d7 | contextual keywords — FIXED |
| 2 (m2) | ab300c6 | non-Lean regression net — BUILT, plant-tested |
| 3 | 9393ffb | clause grouping unified — FIXED, byte-identical |
| 4 (m7) | 97e995f | tuple-let RHS single evaluation — FIXED, red-green pinned |
| 5 (M2) | 9614621 | integerDiv — **VERIFIED-NO-DEFECT**, mapping unchanged, parity pinned (see §M2) |
| 6 (M3) | aa02540 | char escapes — FIXED |
| 7 (M4) | 70873ce | setChoose — MIRRORED comparator-minimum |
| 8 | cc05225 | riders: extra_import echo + reserved names — FIXED |

## Item 1 — M1 contextual keywords (8abf4d7)

Mechanism: the seven fork annotation words stay lexer tokens; the
parser's identifier nonterminal `x` gains one production per token
(contextual-keyword route — the review's first remedy). The tokens are
expected only after `Declare targets_opt`, a position where `x` never
occurs; ocamlyacc conflict counts unchanged (2 shift/reduce,
2 reduce/reduce, 5 never-reduced rules, before and after — derived
from `ocamlyacc -v`).

Positive: all seven words as let-bound names generate correctly for
BOTH `-ocaml` and `-lean` (14/14 probes green, incl. the review's
`let fuel = (1:nat)`); standing test
`tests/comprehensive/test_contextual_keywords.lem` (value names,
function name, parameters, match-pattern variables, record fields,
plus a live `declare {lean} fuel` alongside), 6/6 asserts PASS.
Negative: all pre-existing negative probes stayed green (13/13 at the
item gate). Gotcha fixed en route: the lean-test lakefile's roots list
is EXPLICIT — a generated test not added there builds nothing and its
asserts silently do not run; test added to roots.

## Item 2 — m2 non-Lean regression net (ab300c6)

`make nonlean-regress` → `tests/nonlean-regress/run.sh`: generates the
library corpus (library/Makefile LIBS, 28 files) and every
`tests/backends/*.lem` (23 files) for the 9 non-Lean emitters
(ocaml hol isa coq html tex lem ident tex_all), hashes every artifact
(generated files + captured stdout/stderr) and records every exit
code; committed goldens = 893 artifact rows + 216 exit rows (derived
counts). Any drift exits 1 naming target+file; vacuity-guarded;
absolute repo paths normalized to `LEMROOT` (tex_all headers and
error messages embed them) so manifests are worktree-portable.
Rebaseline is explicit-only (`NONLEAN_REGRESS_REBASELINE=1`).

Baselined AFTER item 1, with the mandated invariance check: the same
script against a scratch build of pre-M1 lem (e591865) —
`PRE/POST-M1 SWEEP: BYTE-IDENTICAL` (893/216 rows). No
stop-and-report: the keyword fix changed no non-Lean output.

Plant evidence (verbatim excerpts):

Emitter plant (extra space in the OCaml backend's `pat_wildcard`,
src/backend.ml:850):

    nonlean-regress: OUTPUT DRIFT (rows are '<sha256>  ./<corpus>/<target>/<file>'):
    -581929a161ca0a10c6e8ff69c40c7afa219b60ebbd7e6e6096f19c7d88b8c8fb  ./backends/ocaml/coq_exps_test/coq_exps_test.ml
    +b8eb8f21fac8e5bb79c7fdf4ea8a4ca979c5151e0d65f88dca8c4866c38d9099  ./backends/ocaml/coq_exps_test/coq_exps_test.ml
    [... further ./backends/ocaml/* and ./lib/ocaml/lem_*.ml rows only ...]

Reverted; net green. Golden plant (one flipped manifest hex digit):

    PERTURBED-GOLDEN NET EXIT: 1
    nonlean-regress: OUTPUT DRIFT (rows are '<sha256>  ./<corpus>/<target>/<file>'):
    -f229ec2bc5ba8d7c3134c92fa650e78290db937ad7f15ad63aa5844f03198053  ./backends/coq/classes.stderr
    +a229ec2bc5ba8d7c3134c92fa650e78290db937ad7f15ad63aa5844f03198053  ./backends/coq/classes.stderr
    nonlean-regress: FAIL — non-Lean emitter output changed; scratch kept at [...]

Restored; `RESTORED NET EXIT: 0`.

The net also TRIPPED once in real use, on item 7's `set_extra.lem`
declare edit (see §Item 7) — first live catch.

## Item 3 — clause-grouping unification (9393ffb)

One shared `lean_group_funcls` (cref-keyed, first-appearance order),
called by both the failwith-thread pre-pass (was cref-keyed inline)
and the Fun_def emission path (was name-STRING-keyed); the supply
pre-pass is the intended third consumer.

**Byte-diff summary (mandated): the tests/comprehensive generated
Lean tree (82 .lean files, sha256 per file) is BYTE-IDENTICAL
before/after — empty diff.** Generation 41/41 both runs;
nonlean-regress green (Lean-path-only change, asserted).

## Item 4 — m7 tuple-let RHS duplication (97e995f)

Multi-name destructuring `Let_def`s emit ONE `private def
lemLetRhs_<names> : <rhs type> := <rhs>` plus per-name projection
defs; single-name lets are byte-identical to the historical emission.
Reader-lifted multi-name lets re-inject reader parameters at the
projections' call of the RHS def; `[Inhabited]` binders ride both.

**Byte-diff summary (mandated): only `Test_let_bindings.lean`
changed, at exactly its 3 multi-name sites** — `(pair_a, pair_b)`,
`(tri_x, tri_y, tri_z)`, `(nest_a, (nest_b, nest_c))` — each gaining
one private RHS def; everything else in the 82-file tree
byte-identical.

Single-evaluation pin (compiled binary, suite phase
`lean-tuple-once`): `let (first_draw, second_draw) = tick_pair ()`
over an effectful counter must bind exactly (1, 2). Finding worth
recording: the reproducer RHS must be ONE opaque effectful call — a
literal-tuple RHS is projection-simplified by the Lean compiler
(measured in the emitted C IR: each old-style duplicated def
evaluates only its own component), which erases sibling draws and
masks the duplication; the review's literal-tuple shape does NOT
reproduce the bug in compiled code.

Red-green evidence (verbatim):

    === m7 single-evaluation pin (tuple-let RHS runs once) ===
      FAIL (exit 1): draws: first=1 second=4
    single-evaluation FAILED: RHS did not run exactly once (got (1, 4), want (1, 2))
    RED-LEG EXIT: 2          [old emitter e591865]

    === m7 single-evaluation pin (tuple-let RHS runs once) ===
      OK: draws: first=1 second=2
    single-evaluation: OK
    GREEN-LEG EXIT: 0        [fixed emitter]

## Item 5 — M2 integerDiv: VERIFIED-NO-DEFECT (9614621) — ESCALATION

The review (M2) and the charter (§8.3 rider) state the OCaml oracle
divides by zarith `Z.div` (truncation) and that Lean's `/` (Int.ediv)
therefore diverges (`(-7)/2 = -3 vs -4`). The slice brief mandated
verifying before touching. **Verified FALSE at the actual call
target.** The chain: `integerDiv` → `Nat_big_num.div`
(library/num.lem:1405) → `BI.div_big_int`
(ocaml-lib/nat_big_num.ml:31) → `Big_int_Z.div_big_int` (zarith's
num-compatibility layer; `ocaml-lib/num_impl_zarith/big_int_impl.ml`
is `include Big_int_Z include Z`) — which is EUCLIDEAN, not `Z.div`.
Measured, verbatim (compiled probes):

    Big_int_Z.div_big_int: (-7,2)->-4 (7,-2)->-3 (-7,-2)->4 (7,2)->3 (-1,3)->-1 (1,-3)->0
    Big_int_Z.mod_big_int: (-7,2)->1 (7,-2)->1 (-7,-2)->1 (7,2)->1 (-1,3)->2 (1,-3)->1
    Z.div: (-7,2)->-3 [...]    (the review's assumed semantics — NOT what lem calls)
    Nat_big_num.div:     (-7,2)->-4 (7,-2)->-3 (-7,-2)->4 (7,2)->3 (-1,3)->-1 (1,-3)->0
    Nat_big_num.modulus: (-7,2)->1  (7,-2)->1  (-7,-2)->1 (7,2)->1 (-1,3)->2  (1,-3)->1

Lean, both deployed toolchains (4.28.0 suite, 4.32.2 cerberus),
verbatim `#eval` plus `rfl` proofs `(/) = Int.ediv`, `(%) = Int.emod`:

    [-4, -3, 4, 3, -1, 0]
    [1, 1, 1, 1, 2, 1]

Perfect agreement at every signed corner; `integerMod` likewise
(erem = emod, independently confirming the review's own mod
observation). Applying the review's remedy (`Int.tdiv`) would have
INTRODUCED the divergence it warns about. Decision [AGENT]: mapping
unchanged; agreement PINNED instead — `test_integer_div.lem` (12
elaborator asserts + operator routes) and compiled-binary
`TestIntegerDivParity` (phase `lean-div-parity`; runtime Int is
GMP-backed, so compiled agreement is asserted, not assumed). The
OCaml-target build of the SAME .lem (linked against ocaml-lib
extract.cmxa) printed, verbatim:

    div: [-4, -3, 4, 3, -1, 0]
    mod: [1, 1, 1, 1, 2, 1]
    op: -4 1

byte-identical to the Lean binary's values.

**Downstream note (charter C1, mandated):** since the mapping is
unchanged, NO generated-Lean semantics change reaches cerberus-lean
from this item at the next pin bump; the C1 differential battery
carries no M2 signature. **Operator attention:** the review's M2
entry and the charter's §8.3 rider carry a wrong factual premise and
should be corrected/annotated at the next charter revision
(review-record correction is an operator call — the review is a
committed verbatim record).

## Item 6 — M3 char escapes (aa02540)

`L_char` now renders via `lean_char_escape` (Char.escaped-compatible
for ASCII printables + named controls; `\xHH` for
non-printable/non-ASCII — the latin1 embedding). The paired
`lean_string_escape` hardened: control bytes < 0x20 hex-escaped;
bytes 0x80–0xFF deliberately still pass through RAW, now documented
in-code — lem's lexer admits only UTF-8 source, so those bytes occur
only inside multi-byte UTF-8 sequences, and per-byte `\xHH` (a
Unicode scalar in Lean, not a byte) would decode-shift the text.

Review reproducer `#'\200'`: old emitter emits `'\200'` /
`'\000'` (verbatim, invalid Lean); fixed emitter `'\xc8'` /
`'\x00'`. New test section in `test_strings_chars.lem` (NUL, SOH,
DEL, 0xFF, decimal-vs-hex cross-notation equalities), 4/4 PASS.
Tree diff: pure append to Test_strings_chars(.aux); pre-existing
generated content byte-identical (no churn from the escaping change
on the existing corpus).

## Item 7 — M4 setChoose (70873ce) — the decision

**Decision [AGENT]: mirror comparator-minimum** (the preferred
remedy). Evidence for feasibility: the set representation is a
duplicate-free list, so min-by-comparator is a fold, and
comparator-EQ ties cannot arise (representation invariant); the
comparator reaches the call site by the established `setElemCompare`
splicing pattern (library/set.lem:352-355, the `insert`/`setAddBy`
precedent) — so the document-the-divergence fallback was not needed.
`setChoose` now takes the comparator and returns the minimum,
mirroring `Pset.choose = min_elt` (ocaml-lib/pset.ml:297,358);
set_extra.lem's Lean rep becomes
``declare lean target_rep function choose s = `setChoose` `setElemCompare` s``.
Pin: `choose {6;1;2} = 1`, `choose {5} = 5` (test_collections.lem),
PASS.

The nonlean net TRIPPED on this edit (first live catch): drifted rows
were exclusively source-echoing targets (tex/tex_all/html/-lem/ident)
re-rendering the edited declare line (verified verbatim in the -lem
echo: the line-26 declare only); the semantic emitters
(ocaml/hol/isa/coq) had ZERO drifted rows. Goldens rebaselined in the
same commit per the net's protocol.

**Downstream note (C1):** at the next pin bump, generated call sites
of `choose` change text and cerberus `Core_linking.topo_order`'s
Lean-side choice changes from newest-head to comparator-minimum —
expected to MATCH the oracle where it previously diverged. Any
linked-emission-order baseline movement in the C1 battery is this
item's expected signature; a differential pin on topo_order-affected
outputs at C1 is recommended.

## Item 8 — riders (cc05225)

- m1: `Decl_extra_import` human-target echo now emits the backtick
  form; round-trip verified (echo re-parses, rc=0; pre-fix: syntax
  error at the quote).
- Reserved-name contract, new generated-def-name leg
  (`lean_check_reserved_def_name`, enforced at Fun_def and Let_def
  emission): `lemDefaultFuel` (silently rebinds every fuel wrapper's
  budget) and the `lemLetRhs_` prefix (item 4's synthesized family —
  collision now a located generation-time error instead of a Lean
  duplicate-def error). Negative probes `neg_default_fuel_name.lem`,
  `neg_let_rhs_name.lem` assert the declared fragments; suite is now
  15/15 negative.

## Close-out battery (final HEAD cc05225, verbatim)

    CLOSEOUT MAKE EXIT: 0
    === Generation: 43 passed, 0 failed, 0 skipped ===
    Build completed successfully (123 jobs).
      OK (leg 1): panic prints the Incomplete Pattern message, then continues with default
      OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1
    single-evaluation: OK
      OK: parity holds (Euclidean, both targets)
    15                      [count of "OK (rejected as declared)" — 15/15 negative probes]
    nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)

lean-lib: `Build completed successfully (35 jobs).` (capped lake
build). Note on counts vs the brief: generation is 43 (was 40) and
negatives 15 (were 13) because this slice ADDED three test files and
two probes; all pre-existing rows stayed green throughout.

Charter-constraint check: no per-declaration fuel-budget semantics
were touched — unannotated declarations' `lemDefaultFuel` behavior is
byte-for-byte unchanged (the only lemDefaultFuel change is the new
fail-closed name-collision guard).

Scratch hygiene: the slice scratch (`.l0-scratch/`, incl. the
e591865 comparison build) is ephemeral and deleted at slice end; all
evidence worth keeping is quoted above or committed as tests.

**Honesty note (appended 2026-09-03, parity-fix slice).** The
"compiled-binary TestIntegerDivParity" leg described above compared
Lean's runtime values against values that were MEASURED BY HAND from a
separate OCaml probe and then written into the Lean test as literals;
it never built or ran an OCaml binary itself, so it was a
self-consistency check against a transcription, not a two-target
test. The values were correct (the parity-fix slice's real runner
confirms the `integer` row byte-for-byte), but the mechanism was not
what the name suggested. The scaffold is retired; the compiled leg now
runs through `tests/comprehensive/parity/run.sh` (suite phase
`lean-parity`), which builds the OCaml reference binary and the Lean
binary from the same `.lem` on every run and diffs their outputs
(`parity/probes/p_num_div.lem`, pin `parity/expected/p_num_div.out`).
That same runner exposed the neighbouring defect this record did not
see: lem `int`/`int32`/`int64` division is NOT Euclidean on the OCaml
target (F1 of the parity-fix record).
