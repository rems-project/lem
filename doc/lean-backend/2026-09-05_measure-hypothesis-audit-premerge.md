# Pre-merge audit — `arc/measure-hypothesis` (lem-lean), 2026-09-05

Auditor [AGENT], independent of the slice's worker. Range audited:
`d4ba548` (mainline `mdd/lean-backend`) → `906ac21` (branch head; 2
commits: `c56785a` the `assuming` clause + tokenizer + projection
refusal, `906ac21` the record). Worktree
`worktrees/lem-lean-audit/measure-hypothesis-premerge` (branch
`audit/measure-hypothesis-premerge` @ `906ac21`), fresh serial `make` of
lem there (`Lem 906ac21`); baseline lem rebuilt from `git archive
d4ba548` (`.tmp/lem-base`, `make` EXIT 0, `Lem d4ba548`). Nothing
merged, nothing pushed; cerberus-lean read-only (primary @ `928aa1e76`,
`git status --short` empty before and after; the dry run is on a copy of
the `LEM_SRC_LEAN` files under `.tmp/cerb`). Every quoted output below is
verbatim from this worktree (`.tmp/*.log`, `.tmp/plants/`, `.tmp/ident/`,
`.tmp/cerb/`); tallies marked "derived" are derived. Findings are
claims: each carries its measurement. `.tmp/` is ephemeral.

## Verdict

**MERGEABLE (ff-only), with ONE condition to be carried to the cerberus
half (F1), one one-line fix recommended before or immediately after
merge (F4: three letter-like ranges missing from the tokenizer's table),
and two record errata (F2, F3).** No non-Lean emitter change
(nonlean-regress byte-identical, the invariance witness holds, the OCaml
output of a hypothesis-carrying `.lem` is byte-identical to the
unconditional form); the wrapper is byte-identical to the unconditional
form; the hypothesis cannot reach execution or the fuel (it is rendered
only into the obligation, before `lemFuel` is bound; the reserved-name
scan refuses `lemFuel`/`LemFuel`/`lemMeasureLe`/`lemHyp`/`_lem…` as any
dotted component); the cerberus tree regenerated with the two lems is
86/86 (OCaml) and 170/170 (Lean) byte-identical; the cerberus
`FuelFormsTool` shape check accepts the new form as MEASURED (read, with
the line numbers, §3); all gates green (§6).

The one substantive finding is a property of the mechanism the ruling
chose, not a bug in its implementation: the vacuity refusal catches the
LITERALS `True`/`False`, but a CONTRADICTORY hypothesis over a parameter
(`b < b`, `b ≠ b`, `(n + 1) ≤ 0`, `2 ≤ b ∧ b ≤ 1`) is accepted, and it
makes the obligation trivially provable — a fuel-free wrapper then
carries the MEASURED mark with a theorem that certifies nothing. No
generation-time rule can close this (satisfiability of a Lean Prop is
not the backend's to decide); the closure is a POLICY on the consumer:
the hypotheses in force must be listed by the gate and reviewed. The
record recommends exactly that as an optional "policy choice" (§2.2,
§8.1); this audit says it is a REQUIREMENT of the cerberus half before
the first `assuming` row lands there. Graded MAJOR by the scope's letter
("a way to make an obligation trivially provable through the
hypothesis"), disposition: not a lem-lean merge blocker (the merge ships
no hypothesis; the hole materialises only when a consumer writes one),
closed by the cerberus-half requirement and a record erratum.

## Findings

### MAJOR

**F1 (MAJOR by the scope's letter; disposition: cerberus-half
requirement + record erratum, no lem code change). A contradictory
hypothesis is accepted and makes the obligation vacuously provable; the
literal-only vacuity check is a speedbump, not a gate.** Plants, verbatim
(`.tmp/plants/plants.log`; each is `test_fuel_measure_hyp.lem`'s
`ndigits` with the hypothesis swapped):

```
=== p01_false.lem EXIT 1
  Error: Lean backend: the measure hypothesis of ndigits is `False` (FH-vacuous: `True` is the unconditional form — write the measure without `assuming`; `False` would make the obligation say nothing)
=== p02_taut.lem EXIT 0                      -- assuming `b = b`
=== p03_measure_le0.lem EXIT 0               -- assuming `(n + 1) ≤ 0`
=== p04_contra.lem EXIT 0                    -- assuming `2 ≤ b ∧ b ≤ 1`
=== p10_false_conj.lem EXIT 1                -- assuming `False ∨ 2 ≤ b`  (refused: the token `False`)
=== p18_neq.lem EXIT 0                       -- assuming `b ≠ b`
=== p19_ne_true.lem EXIT 1                   -- assuming `b = b → False`  (refused: the token `False`)
=== p20_lt_irrefl.lem EXIT 0                 -- assuming `b < b`
```

The generated obligations (`.tmp/plants/out/*/…_auxiliary.lean`):

```lean
theorem ndigits_measure_sufficient ( b : Nat) ( n : Nat) (lemHyp : ((n + 1) ≤ 0)) (lemFuel : Nat) (lemMeasureLe : (n + 1) ≤ lemFuel) :
theorem ndigits_measure_sufficient ( b : Nat) ( n : Nat) (lemHyp : (b < b)) (lemFuel : Nat) (lemMeasureLe : (n + 1) ≤ lemFuel) :
```

Each is provable by `absurd lemHyp (Nat.lt_irrefl _)` / `omega` with no
stability argument, ships the fuel-free wrapper `def ndigits b n :=
ndigits_lemFuel (n + 1) b n`, and the cerberus tool (§3) classifies it
MEASURED with `axioms=ok`. Assessment, honestly:

- *Self-limiting for reasoning consumers*: a downstream theorem must
  supply `lemHyp`, which is unsatisfiable, so the certificate is unusable
  — nobody can be misled INTO a proof by it.
- *Not self-limiting for the gate*: before this slice the only routes to
  MEASURED without a real proof were `sorry`/`axiom` (gate-caught). The
  hypothesis is a third route that no lem-side or cerberus-side gate
  catches, and the record's §2.3 "what the syntactic rules do not catch"
  names only the harmless direction (`b = b`, "the proof is then no
  easier"); the `False` message ("would make the obligation say nothing")
  shows the intent but only the literal is caught (p19 vs p18 shows the
  check is token-based, not semantic).
- *Execution*: unchanged either way — the wrapper is the same fuel-free
  form; on inputs where μ is insufficient the sentinel fires (loud in
  production). So the hole is in the CERTIFICATE, not the exec cone.

Required of the cerberus half (carry to its charter): the `FuelFormsTool`
detail column reports `hyp=<H>` for every MEASURED row whose obligation
has the `lemHyp` binder, and the register of hypotheses in force is a
REVIEWED artifact (each hypothesis a frontend-guaranteed invariant with a
citation, e.g. §5 below), not an optional policy. Recommended for the
record (erratum, docs-only): §2.3's "by design" paragraph names the
contradictory direction and points at the register.

### MINOR

**F2 (MINOR, docs). TODO row 20 misquotes the non-Prop failure.** Row 20
says the auxiliary file fails with "`type expected`"; the record §5.4 and
this audit's reproduction (Lean 4.28.0, `lean-lib` `lake env lean` on the
generated module + the obligation stated as a `Prop`-valued `example`,
`.tmp/plants/elab/p11_nonprop.lean`) say:

```
../.tmp/plants/elab/p11_nonprop.lean:38:41: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  HAdd Nat Nat (Sort ?u.454)
EXIT 1
```

(the honest `2 ≤ b` statement elaborates: `p00_ok` EXIT 0). The claim
that a non-Prop hypothesis is a BUILD error is confirmed; generation
accepts it (`p11_nonprop.lem EXIT 0`). Generation-time detection is not
feasible without typing Lean text — the designed limit stands; fix the
row's quote.

**F3 (MINOR, docs). Record §5.5 says lean-lib's build prints "its twelve
`#print axioms` lines as before".** The capped `lake build` here prints
23 `depends on axioms` lines (`.tmp/gate-leanlib.log`; 27 `#print axioms`
in the sources). lean-lib is unchanged by the slice (`git diff
d4ba548..906ac21 --stat -- lean-lib` empty), so nothing is wrong with
the library; the count in the record is wrong.

**F4 (MINOR, code — one line). `lean_is_letter_like` is NOT Lean's
`isLetterLike` ∪ `isSubScriptAlnum`: three ranges are missing.** Checked
against the toolchain sources (`~/.elan/toolchains/leanprover--lean4---v4.28.0/src/lean/Init/Meta/Defs.lean:100–118`
and the same in `v4.32.2`, lines 108–118 — both toolchains agree):

```lean
  (0x00c0 ≤ c.val && c.val ≤ 0x00ff && c.val ≠ 0x00d7 && c.val ≠ 0x00f7) || -- Latin-1 supplement letters but × and ÷
  (0x0100 ≤ c.val && c.val ≤ 0x017f)                                        -- Latin Extended-A
  ...
  c.val == 0x2c7c                                                            -- (isSubScriptAlnum)
```

`src/lean_backend.ml` `lean_is_letter_like` (the slice's table) has the
Greek/Coptic/polytonic/letterlike/script and three subscript ranges only.
Consequence: a Latin-1 or Extended-A letter is classified `Other` and
PASSES THROUGH as an operator, so it neither joins an identifier nor is
checked as one — FH-free is evadable at generation. Plants, verbatim
(`.tmp/plants/plants.log`):

```
=== p30_latin1.lem EXIT 0                    -- assuming `2 ≤ ñ ∧ 2 ≤ b`   (ñ evades FH-free)
theorem ndigits_measure_sufficient ( b : Nat) ( n : Nat) (lemHyp : (2 ≤ ñ ∧ 2 ≤ b)) (lemFuel : Nat) (lemMeasureLe
=== p31_modifier_j.lem EXIT 0                -- assuming `2 ≤ bⱼ`          (rendered `b` + `ⱼ`; Lean reads one identifier `bⱼ`)
theorem ndigits_measure_sufficient ( b : Nat) ( n : Nat) (lemHyp : (2 ≤ bⱼ)) (lemFuel : Nat) (lemMeasureLe : (n + 1)
=== p32_latin1_alone.lem EXIT 1              -- assuming `2 ≤ ñ`           (caught, but by FH-vacuous, not FH-free)
```

Fail-closed at the BUILD in every case (`ñ`/`bⱼ` are unknown identifiers
to Lean; a lem parameter cannot carry them), and no existing output can
change (N7: no non-ASCII in any backtick declare in cerberus or the lem
corpus; §4 byte-identity). So: MINOR, not a merge blocker; the record's
§2.4 claim "classifies them by Lean's own `isLetterLike`/
`isSubScriptAlnum`" is inaccurate until the three ranges are added (one
line), and the plant p30 should become a negative probe once they are.

### NOTE

**N1. The cerberus gate accepts the new form; its shape check is looser
than its comment says (pre-existing).** `FuelFormsTool.lean:121–150`
(`obligationShapeMismatch`): walks the ∀-telescope (`telescope`, line
122), checks the conclusion's heads by constant name, then (lines
136–148) looks for ANY binder `LE.le _ _ _ (bvar i)` whose bound variable
is a `Nat` binder that occurs as an argument of the worker side. For the
new form (binders `b, n, lemHyp, lemFuel, lemMeasureLe`; n = 5) the
`lemMeasureLe` binder at k = 4 has `args[3] = bvar 0` → j = 3 →
`binders[3] = Nat`, and `lemFuel` is `bvar 1` in the lhs → `found`. So
the extra Prop binder is transparent to the check; MEASURED. (It is also
satisfied at k = 2 by `2 ≤ b` itself, since `b` is a Nat parameter the
worker takes — the check does not pin the fuel POSITION or NAME; a
pre-existing looseness the `hyp=` report of F1 should tighten by reading
the binder named `lemHyp`.) `scripts/check_fuel_forms.sh` is table-driven
(no text pattern on binder order): unaffected.

**N2. Binders inside a hypothesis are refused as free variables.**
`∀ k, k ≤ n` → ``free variable `k` `` (p12); `fun x => x` → ``free
variable `fun` `` (p17); `let y := b; 2 ≤ y` → ``free variable `let` ``
(p05). A hypothesis with its own binders must be a NAMED consumer-side
predicate (`Ns.Acyclic env`) — consistent with the design's "a Prop the
consumer-side module defines"; worth one line in the manual.

**N3. Numerals in a hypothesis are accepted** (`n ≤ 1000`, p16, EXIT 0).
They cannot reach execution (the hypothesis is rendered only into the
obligation) and only narrow the theorem's domain; not a magic value in
the ruled sense, but visible in the `hyp=` register (F1).

**N4. Refusals confirmed** (each EXIT 1 with the declared tag):
`lemHyp` / `Foo.lemHyp b` / `lemFuel ≤ n` / `Foo.lemFuel n` /
`lemMeasureLe` / `Foo._lemReader_x b` → "mentions the reserved binder";
`LemFuel.fuel ≤ n` → FH-ambient; `_root_.Nat.le 2 b` → FH-root; `sizeOf n
≤ 3` → FH-sizeOf; `2 ≤ β`, `2 ≤ b₁` → FH-free (the tokenizer reads them
as identifiers, as Lean would); `Foo.Bar.1 ≤ b` → the projection refusal;
a parameter named `lemHyp` (p24) → "binder 'lemHyp' collides with a
reserved synthesized binder"; a constant whose Lean `target_rep` is
`lemHyp` referenced in a fuel'd body (p25 measured, p26 unmeasured) →
"renders on Lean as `lemHyp` — a reserved synthesized binder name". The
last is conservative (the body is never under the obligation's binder),
harmless. `True ∧ 2 ≤ b` is refused (token `True`) — an over-refusal in
the safe direction.

**N5. Qualified names are trusted at generation, as for measures.**
`Nat.False b` (p15) generates (EXIT 0) and would fail at build (unknown
identifier) — fail-closed at the build, by the existing design.

**N6. Duplicate `fuel_measure` declares on one val: last wins silently**
(p28: an unconditional declare followed by an `assuming` one → the
obligation carries `lemHyp`). Pre-existing `Targetmap.insert` semantics;
the slice widens what a later declare can change. Speedbump candidate,
not this slice's.

**N7. Tokenizer.** Beyond F4 (the missing ranges), the ranges the
table does have match Lean's. One further divergence: subscripts are
identifier START characters here (Lean: continuation only), so a
hypothesis beginning with `₁` becomes an identifier and is refused
FH-free rather than passed through — harmless. The old tokenizer's behaviour differs from the new
only on non-ASCII bytes inside a measure/hypothesis string: `grep -rnP`
over cerberus `frontend/model/*.lem` finds NO backtick declare with a
non-ASCII character (non-ASCII appears only in comments/strings, which
the tokenizer never sees), and none in lem's `tests/`, `library/`,
`examples/` outside the slice's own files — so no existing output can
change, and §4's byte-identity is the measurement.

**N8. A `"` inside a backticked hypothesis is a lem lexical error**
(p21: ``Lexical error: unknown character ` ``) — pre-existing backtick
string lexing; string literals in a hypothesis are not possible.

**N9. `assuming` as an identifier.** `test_contextual_keywords.lem` (a
let-name, a parameter, a record field, and the clause) generates for
OCaml here: `-ocaml EXIT 0`. `declare {ocaml} fuel_measure … assuming
…` (p27) and the target-less `declare fuel_measure … assuming …` (p29)
are accepted and the OCaml output is byte-identical to the unconditional
form (modulo the file-name header).

**N10. Parallel `make -j4` of lem races** (`lexer.mll: Unbound module
Parser`, EXIT 2; serial `make` EXIT 0). Pre-existing ocamlbuild
parallelism, not this slice's; noted so the next auditor does not chase
it. ocamlyacc at both `parser.mly`s: `5 rules never reduced 2
shift/reduce conflicts, 2 reduce/reduce conflicts.` — unchanged.

**N11. `count_list_bounded_measure_sufficient`
(`Test_contextual_keywords_lemMeasureProofs.lean`) has no `#print
axioms` pin** (the three `Test_fuel_measure_hyp` proofs do). Covered by
the no-sorry/axiom token scan and the build; a pin would be uniform.

## 1. The clause — what was planted (summary; verbatim in F1/N4)

33 plants (`.tmp/plants/p*.lem`): the refusals of §2.3 of the record all
fire with their declared tags; the accepted set is {`2 ≤ b` (control),
`b = b`, `(n + 1) ≤ 0`, `2 ≤ b ∧ b ≤ 1`, `n + 1` (non-Prop), `Nat.False
b`, `n ≤ 1000`, `b ≠ b`, `b < b`, `b.succ.succ ≤ 4`, two declares, the
OCaml-target and target-less declares}. Of these only the contradictions
(F1), the non-Prop (F2, build-caught) and the Latin-1 letters (F4,
build-caught) are of interest.

## 2. The wrapper and the obligation shell — byte-identity

`p00_before.lem` (no `assuming`) vs `p00_ok.lem` (`assuming `2 ≤ b``),
generated here; `diff` of the modules:

```
1c1
< /- Generated by Lem from p00_before.lem. -/
---
> /- Generated by Lem from p00_ok.lem. -/
```

(the header only); the wrapper line in both: `def ndigits ( b : Nat) ( n
: Nat) : Nat := ndigits_lemFuel (n + 1)  b  n`. The auxiliary files differ
in the header/imports and exactly the obligation:

```lean
theorem ndigits_measure_sufficient ( b : Nat) ( n : Nat) (lemHyp : (2 ≤ b)) (lemFuel : Nat) (lemMeasureLe : (n + 1) ≤ lemFuel) :
    ndigits_lemFuel lemFuel  b  n = ndigits  b  n :=
  P00_ok_lemMeasureProofs.ndigits_measure_sufficient  b  n lemHyp lemFuel lemMeasureLe
```

`lemHyp` immediately before `lemFuel`; the delegation passes `lemHyp` in
that position. Matches the record §3.

## 3. Cerberus gate compatibility

Read `cerberus-lean/lean_frontend/test/Unit/FuelFormsTool.lean` @
`928aa1e76`; analysis in N1: the new form is MEASURED. No blocker for
the cerberus half from the shape check. The hand-written seam shape of
record §6.4 (`(lemHyp : H) (lemFuel : Nat) (lemMeasureLe : μ ≤ lemFuel)`)
is the same telescope and passes for the same reason.

## 4. Tokenizer + projection — byte-identity of the cerberus tree

`LEM_SRC` (86 files) and `LEM_SRC_LEAN` (85 files) obtained with `make
--eval` from the read-only primary; both lems run from the cerberus
directory with the Makefile's flags (`-wl ign -wl_rename warn
-wl_pat_red err -wl_pat_exh warn -cerberus_pp`, `-outdir` under
`.tmp/ident/`); verbatim (`.tmp/ident/summary.txt`):

```
base ocaml exit 0 files 86
base lean exit 0 files 170
final ocaml exit 0 files 86
final lean exit 0 files 170
OCAML DIFF (cerberus frontend @ 928aa1e76, lem d4ba548 vs 906ac21) exit 0 lines 0
LEAN DIFF (same) exit 0 lines 0
cerberus status lines: 0
```

Reproduces the record §5.6. Corpus grep for non-ASCII inside backtick
declares: none (N7).

## 5. The 13-row dry run

**Reproduced (generation).** Copy of the 85 `LEM_SRC_LEAN` files under
`.tmp/cerb`; the four declares of the record's rows 7–9 and 13 added
after the existing `fuel val` declares in `ctype_aux.lem` (with `declare
{lean} extra_import `CerbTagsWf``) and `formatted.lem`; generation with
this lem: `dry-run lean-after exit 0 files 170`; `[LemFuel]` binders
240 (derived; the record: 251 → 240); 7 modules differ from the
unpatched tree (`Core_aux`, `Core_aux_auxiliary`, `Core_reduction`,
`Ctype_aux`, `Ctype_aux_auxiliary`, `Formatted`, `Formatted_auxiliary`
— the record's list). The four obligations are byte-for-byte the
record's §6.3 statements (e.g. `Ctype_aux_auxiliary.lean:48`
`are_compatible_aux_measure_sufficient … (lemHyp : (CerbTagsWf.Acyclic
p.1 ∧ CerbTagsWf.Acyclic p.2)) (lemFuel : Nat) (lemMeasureLe :
(CerbTagsWf.envBound p.1 p0.2 + CerbTagsWf.envBound p.2 p1.2 + 1) ≤
lemFuel)`), and the wrappers are fuel-free. NOT reproduced: the scratch
Lean build of the dry run (record §6.1) — out of this audit's footprint.

**The hand-written rows' proposals (`Acyclic`, `envBound`) are
well-defined, and `Acyclic` IS a frontend guarantee.** `Acyclic m := ∃
rank, ∀ (tag, (_, d)) ∈ m, ∀ member c of d, ∀ t ∈ refsOf c, rank t <
rank tag`, with `refsOf` the by-VALUE tag references (`Struct`/`Union`
tags reached through `Array`/`Atomic`, never through `Pointer` or a
function type) — a rank function on the tag environment; `envBound m ty
:= (tagCount m + 1) * (ctype.lemSize ty + defsSize m + 1)` is a Nat
expression over the parameters. Why the frontend guarantees it:
`cabs_to_ail.lem:1512` `check_members` (STD §6.7.2.1#3) refuses a
member whose type is a function
(`StructMemberFunctionType`) or INCOMPLETE (`StructMemberIncompleteType`;
the flexible array member's element type likewise at 1600–1603);
`AilTypesAux.is_complete` (`ail/ailTypesAux.lem:222`) says a `Pointer` is
complete regardless of its target, an `Array` is complete iff its
element type is and its size is known, `Atomic` iff its inner type is,
and `Struct sym`/`Union sym` iff `sym` is ALREADY in
`sigm.tag_definitions`. Hence at the moment a tag's definition is
accepted, every by-value reference in its members points to a tag
defined EARLIER; the position in definition order is a rank; pointers
break the recursion (`struct A { struct B *p; }; struct B { struct A a;
};` is fine: B refs A by value, A refs B only through a pointer). A
hand-authored Core file can violate it (the record says so), which is
exactly why the hypothesis belongs in the obligation rather than being
assumed by the wrapper.

Rows 10–12 (`hack`, `many`, `many1`): the record's "no hypothesis on the
parameters bounds them" is correct as argued there (the bound is a fact
about an evaluation, not about the parameters); they stay P.

## 6. Gates — verbatim

**`tests/comprehensive` `make clean; make lean`** (`.tmp/gate-make-lean.log`):

```
=== Generation: 54 passed, 0 failed, 0 skipped ===
Build completed successfully (165 jobs).
  OK (leg 1): panic prints the Incomplete Pattern message, then continues with default
  OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1
single-evaluation: OK
  OK: compiled draw sequences hold
  OK: compiled consumer injection holds
  OK (leg 1): two sufficient fuels agree; insufficient gives the declared sentinel; callee starts from the full ambient
  OK (leg 2): loud exhaustion at an insufficient runtime fuel fail-stops (exit 134)
  OK: inv_fuel_measure_hyp.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
=== p_fuel_measure_hyp ===
  OK: parity (9 lines byte-identical to the OCaml reference; pin matches)
  OK: 10 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
  OK: 254 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make lean  588.14s user 69.56s system 114% cpu 9:34.54 total
EXIT 0
```

Derived: 97 × `OK (rejected as declared)` (11 of them the slice's new
probes), parity 26 OK / 6 both-fail / 4 XFAIL (the 4 `FAIL` lines are the
registered XFAILs), 8 invariance OK, 680 `PASS:` asserts (among them
`PASS: ndigits_ok`, `uses_ndigits_ok`, `size_of_ok`, `down_steps_ok`,
`ctx_kw_assuming_decl_ok`), 0 `declaration uses 'sorry'`. Axioms:

```
Test_fuel_measure_hyp_lemMeasureProofs.lean:173:0: 'Test_fuel_measure_hyp_lemMeasureProofs.ndigits_measure_sufficient' depends on axioms: [propext, Quot.sound]
Test_fuel_measure_hyp_lemMeasureProofs.lean:174:0: 'Test_fuel_measure_hyp_lemMeasureProofs.size_of_measure_sufficient' depends on axioms: [propext, Quot.sound]
Test_fuel_measure_hyp_lemMeasureProofs.lean:175:0: 'Test_fuel_measure_hyp_lemMeasureProofs.down_steps_measure_sufficient' depends on axioms: [propext, Quot.sound]
```

**`make nonlean-regress`** (`.tmp/gate-nonlean.log`):

```
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
EXIT 0
```

**lean-lib** (`CERB_MEM_MAX=16G capped lake build`, `.tmp/gate-leanlib.log`):
`Build completed successfully (39 jobs).` `EXIT 0`; 23 `depends on
axioms` lines, every cone ⊆ {propext, Classical.choice, Quot.sound};
`grep -rn '^axiom ' lean-lib --include='*.lean'`: 0.

**OCaml byte-diff**: §4 (86/86) and N9.

## 7. Not checked

- The scratch Lean BUILD of the cerberus dry run (record §6.1) and the
  `CerbTagsWf`/`CerbMemHypShape` scratch seams — generation reproduced
  only.
- The record's §5.3 missing-proofs plant (deleting a theorem) — not
  re-run; the mechanism is the pre-existing one.
- The cerberus-side proofs, seams, and gate changes (by charter, the
  cerberus half's).
- The contents of the three hypothesis proofs beyond their axiom cones
  and the suite's kernel pins (`TestFuelMeasureHypCheck`) — read, not
  re-derived.
