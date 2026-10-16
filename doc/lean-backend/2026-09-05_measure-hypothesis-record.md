# Measure-hypothesis slice — record (2026-09-05)

Branch `arc/measure-hypothesis` (lem-lean), from mainline `mdd/lean-backend`
@ `d4ba548`. Charter: the `fuel_measure` obligation gains an optional
HYPOTHESIS on the parameters, so measures whose sufficiency depends on a
well-formedness or precondition fact become provable — the lem side of
D-C2-1 in cerberus's `lean_frontend/docs/2026-09-04_fuel-parameter-C2-record.md`
§9. Worker [AGENT] (lem-lean); the ruling quoted with [USER] provenance;
every quoted output is verbatim from this worktree (`.tmp/` logs named);
tallies marked "derived" are derived. Nothing merged, nothing pushed;
cerberus-lean read-only (the dry run is on a scratch copy under `.tmp/`).

## 0. Commits

| Commit | Content |
|---|---|
| `c56785a` | the `assuming` clause: lexer/parser/ast/typed_ast/typecheck/echo/Ott; backend (`lean_render_param_expr` — the measure renderer generalised to measure/hypothesis kinds, the `lemHyp` obligation binder, the reserved name `lemHyp`, the UTF-8 letter-like tokenizer, the projection-on-non-parameter refusal); tests (`test_fuel_measure_hyp.lem` + `TestFuelMeasureHypImpl` + proofs + kernel pins, 11 negatives, invariance witness, parity probe + proofs + NEW pin, `assuming` in the contextual-keywords test with `count_list_bounded` + proof); manual, DESIGN, README, TODO rows 20–22 (+ row 18 note), design note R4 |
| `906ac21` | this record |
| (audit-response commit) | pre-merge audit response (§10): F4 the three missing letter-like ranges + `neg_fuel_measure_hyp_latin1`; F1 the contradictory-hypothesis erratum in record/manual/DESIGN + TODO row 23 (cerberus-half requirement); F2 TODO row 20's quote; F3 §5.5's count; N11 `#print axioms` pins in the contextual-keywords proofs module |

## 1. The ruling this slice implements

[USER 2026-09-05] (as relayed in the charter) agreed to proceed with
option 1 — the orchestrator's D-C2-1 recommendation: a
hypothesis-carrying obligation form on the lem side — extend the measure
declare so it can name a hypothesis on the parameters (a predicate the
consumer-side module defines); the generated obligation becomes `H xs → μ
xs ≤ fuel → f_lemFuel fuel xs = f xs`; Lean-only, no `.lem` body change;
the wrapper stays fuel-free. Standing rules, all kept: the lem structure
is not changed for OCaml's sake (OCaml and every other emitter byte-identical,
§5.5/§5.6); no magic values; zero axioms; kernel-only proofs; the three
admissible forms (caller parameter / termination proof / data measure)
and the consumer's (A)/(B)/(C) requirement.

## 2. Design — decisions, reasons, alternatives

### 2.1 The declare: ``declare {lean} fuel_measure val f = `<measure>` assuming `<H>` ``

One declaration, one clause: the hypothesis rides on the measure it
qualifies (`const_descr.fuel_measure : (string * string option)
Targetmap.t`; `Decl_fuel_measure_decl` gains the optional `(terminal *
(terminal * string))`). `assuming` is a contextual keyword like the
others (`test_contextual_keywords.lem`: let-name, parameter, record
field, and the clause beside them; `-ocaml` of that file generates —
the word is an identifier everywhere but after a backticked measure).
Two refusal productions give the two mis-uses their reasons at parse:
`fuel_measure val f assuming `H`` without a measure ("has no measure"),
and `assuming` on the fuel SENTINEL declare ("not part of the fuel
sentinel declare"). ocamlyacc at the final grammar, verbatim
(`.tmp/build4.log`): `5 rules never reduced` / `2 shift/reduce
conflicts, 2 reduce/reduce conflicts.` — unchanged from `d4ba548`.

**Alternatives considered.** (i) A separate declare (`declare {lean}
measure_hypothesis val f = `H``) — a second cross-check ("hypothesis
without a measure") and a second Targetmap for one fact; rejected.
(ii) A keyword other than `assuming` (`given`, `under`, `if`): `if` is
a real lem keyword (no new token, but `= `m` if `H`` reads as a
conditional measure, which it is not); `assuming` states what the
obligation does. (iii) Putting the hypothesis INSIDE the measure
backticks with a separator — hides a Prop in a Nat expression's syntax.

### 2.2 What the hypothesis renders to — the wrapper unchanged, the obligation's `lemHyp` binder

`H` is a Lean Prop over the function's parameters, rendered by the same
renderer as the measure (`lean_render_param_expr`, kind `LPE_hypothesis`:
same tokenizer, same scope rules — parameters by their lem names,
qualified globals, `lemSize x` —, same forbidden names). The WRAPPER is
byte-identical to the unconditional form (§3): fuel-free, hypothesis-
free; `f` and its consumers carry nothing. The OBLIGATION gains `H` as
the binder NAMED `lemHyp`, immediately before `lemFuel`, and the
delegation passes it in that position:

```lean
theorem f_measure_sufficient (xs…) (lemHyp : (H)) (lemFuel : Nat) (lemMeasureLe : (μ) ≤ lemFuel) :
    f_lemFuel lemFuel xs… = f xs… :=
  <Module>_lemMeasureProofs.f_measure_sufficient xs… lemHyp lemFuel lemMeasureLe
```

**The exact shape, for cerberus's gate** (`scripts/check_fuel_forms.sh`
/ `FuelFormsTool.obligationShapeMismatch`, which today checks: ∀-telescope,
conclusion `worker … = wrapper …` with the heads compared by constant
name, and some binder `_ ≤ lemFuel` on a `Nat` binder the worker side
takes — the hypothesis-carrying form ALREADY satisfies that check, so it
is classified MEASURED unchanged). To tell the two forms apart
deterministically: the conditional form has a binder whose NAME is
`lemHyp`, whose type is a `Prop` mentioning only the parameters (never
`lemFuel`, which is bound after it), placed immediately before the
`lemFuel : Nat` binder; the unconditional form has no binder of that
name — `lemHyp` is a reserved synthesized name (a parameter or body
binder of a fuel'd definition may not be called `lemHyp`;
`neg_fuel_measure_hyp_reserved_param`), so the mark cannot be produced by
a user variable. A hand-written measured seam that needs a hypothesis
states the same shape by hand (§6.4). Recommended consumer change:
report `hyp=<H>` in the tool's detail column and let the register
distinguish "MEASURED" from "MEASURED under H" — a policy choice for
the cerberus half, not this slice's.

**Operational meaning of `H`.** On inputs violating it the wrapper may
EXHAUST: the worker bottoms out in the declared sentinel after `μ`
frames, and the frames above it compute with that value — pinned in
`TestFuelMeasureHypCheck` (5): `ndigits 1 5 = 6 + 999`, `down_steps (5,
0) = 6 + 999`, `size_of [[0]] 0 = 1 + 999` (a cyclic table), all by
`decide`. With the production sentinel `fuelExhausted` that is the loud
panic instead. This is admissible because the oracle's own behaviour on
those inputs is not the semantics anyone relies on: at basis 1 the OCaml
`showNonNegativeWithBasis_aux` loops forever, at basis 0 it raises; the
frontend never produces a cyclic tag environment (a hand-authored Core
could) — and the consumer's theorems carry `H` exactly as they already
assume well-formedness. Nothing about the exec cone changes: measured
wrappers are fuel-free either way.

### 2.3 Fail-closed rules on the hypothesis (each a negative probe)

| Rule | Refuses | Probe |
|---|---|---|
| FH-vacuous | `True` / `False` (checked before FH-free), or a hypothesis mentioning no parameter (a closed proposition) — `True` is the unconditional form in disguise; the two forms must stay distinct for the gate mark | `neg_fuel_measure_hyp_vacuous`, `neg_fuel_measure_hyp_closed` |
| reserved | `lemFuel`, `lemMeasureLe`, `lemHyp`, `_lem…` as any dotted component — the hypothesis may not mention the fuel | `neg_fuel_measure_hyp_fuel` |
| FH-ambient | `LemFuel` as any component | `neg_fuel_measure_hyp_ambient` |
| FH-free | an unqualified non-parameter | `neg_fuel_measure_hyp_freevar` |
| FH-sizeOf | `sizeOf`/`SizeOf` — one vocabulary for measure and hypothesis ([AGENT] uniformity, not necessity: a Prop is not executed; TODO row 21) | `neg_fuel_measure_hyp_sizeof` |
| FH-root | `_root_` (shared code path with FM-root; no separate probe) | — |
| projection | `q.2` when the parameter is `p`: a numeral component is a projection, never a namespace, so the head must be a parameter — found on the dry run (§6.2), applies to measures too (FM-free) | `neg_fuel_measure_hyp_projection`, `neg_fuel_measure_projection` |
| parse | `assuming` without a measure; `assuming` on the fuel sentinel declare | `neg_fuel_measure_hyp_nomeasure`, `neg_fuel_measure_hyp_on_fuel` |
| reserved binder | a fuel'd definition's parameter named `lemHyp` (joins `lemFuel`/`lemMeasureLe` in `reserved_binder_check` and `lean_reserved_exact_names`) | `neg_fuel_measure_hyp_reserved_param` |
| non-Prop | NOT a generation refusal: the backend cannot type Lean text; the auxiliary file fails to elaborate (§5.4 plant; TODO row 20) | — |

What the syntactic rules do not catch, by design: a hypothesis that
mentions a parameter without constraining it (`b = b`) — the proof is
then no easier; the theorem is the backstop, as for a disguised
parameter-free measure. AND (pre-merge audit F1, MAJOR by the scope's
letter — the first version of this paragraph named only the harmless
direction): a CONTRADICTORY hypothesis — `b < b`, `b ≠ b`, `(n + 1) ≤
0`, `2 ≤ b ∧ b ≤ 1` — is accepted (only the literals `True`/`False` and
a parameter-free hypothesis are refused: the check is token-level, `b =
b → False` is refused for its `False` token while `b ≠ b` is not) and
makes the obligation VACUOUSLY provable (`absurd lemHyp (Nat.lt_irrefl
_)`, `omega`) while the fuel-free wrapper ships with the MEASURED mark
and `axioms=ok`. Satisfiability of a Lean Prop is undecidable at
generation and not the backend's to decide; the certificate, not the
exec cone, is what the hole is in (the wrapper is the same fuel-free
form either way; an insufficient measure fires the loud sentinel). The
closure is a REQUIREMENT of the cerberus half, before its first
`assuming` row: (i) the fuel-forms gate reports `hyp=<H>` for every
MEASURED row whose obligation has the `lemHyp` binder; (ii) a REVIEWED
hypothesis register, each hypothesis named with the frontend invariant
that guarantees it (§10; TODO row 23).

### 2.4 Two renderer changes that reach the measure too

1. **UTF-8 in the tokenizer.** Before this slice every non-ASCII BYTE
   was an identifier character, which made `2 ≤ b` the free variable `≤`
   (first generation of the test, verbatim: ``Error: Lean backend: free
   variable `≤` in the measure hypothesis (`assuming`) of ndigits (FH-free:
   …``). `lean_measure_tokens` now decodes code points and classifies them
   by a table transcribed from Lean's `isLetterLike` ∪ `isSubScriptAlnum`
   (`Init/Meta/Defs.lean`, identical in 4.28.0 and 4.32.2): Latin-1
   supplement letters but × ÷, Latin Extended-A, Greek but λ/Π/Σ,
   Coptic, polytonic Greek, the letterlike block, script/double-struck/
   fraktur, the subscript ranges and U+2C7C — letter-like → identifier
   character; every other code point (`≤ ∧ ∀ → ≠ ∈ ¬ ×`) → passes
   through as an operator. (The first version of the table omitted the
   Latin-1, Extended-A and U+2C7C entries — pre-merge audit F4 — so `ñ`
   passed through and `2 ≤ ñ ∧ 2 ≤ b` reached the build; §10 has the
   plant. One residual divergence, harmless: subscripts START an
   identifier here, continuation-only in Lean.) A measure
   had no need of Unicode operators, so no existing measure changes
   (§5.6: the cerberus Lean tree is byte-identical).
2. **Projection on a non-parameter refused.** `env.1` when the parameter
   is `env1` used to pass as a "qualified global" (namespace `env`, name
   `1`); now any dotted identifier with a numeral component whose head is
   not a parameter is refused with the parameters listed (§6.2).

### 2.5 Plumbing

Lexer (`assuming` → `Assuming`, contextual), parser (token; the `x`
identifier rule; three productions — accept, refuse-without-measure,
refuse-on-fuel), `ast.ml`, `typed_ast.ml(i)` (`Decl_fuel_measure` gains
`(lskips * string) option`; `fuel_measure : (string * string option)
Targetmap.t`), `typecheck.ml`, the human-target echo in `backend.ml`
(` assuming `H``), the Ott row `fuel_measure_hyp_decl` (TODO row 5, the
Ott derived artifacts, pre-existing). Backend: `lean_render_param_expr
kind` with `lean_render_measure`/`lean_render_hypothesis` wrappers; the
`Some (measure, hyp_opt)` branch of the wrapper/obligation emission adds
`hyp_binder`/`hyp_arg`; the generated obligation comment names the
hypothesis and says "on inputs violating it the wrapper may exhaust".

## 3. Before / after — one function, verbatim

`ndigits` (`test_fuel_measure_hyp.lem`), BEFORE = the same source with
`assuming `2 ≤ b`` removed (`.tmp/plant/Test_before*.lean`), AFTER =
`Test_fuel_measure_hyp*.lean`. The wrapper is byte-identical:

```lean
def ndigits ( b : Nat) ( n : Nat) : Nat := ndigits_lemFuel (n + 1)  b  n
```

The obligation, BEFORE:

```lean
theorem ndigits_measure_sufficient ( b : Nat) ( n : Nat) (lemFuel : Nat) (lemMeasureLe : (n + 1) ≤ lemFuel) :
    ndigits_lemFuel lemFuel  b  n = ndigits  b  n :=
  Test_before_lemMeasureProofs.ndigits_measure_sufficient  b  n lemFuel lemMeasureLe
```

AFTER:

```lean
theorem ndigits_measure_sufficient ( b : Nat) ( n : Nat) (lemHyp : (2 ≤ b)) (lemFuel : Nat) (lemMeasureLe : (n + 1) ≤ lemFuel) :
    ndigits_lemFuel lemFuel  b  n = ndigits  b  n :=
  Test_fuel_measure_hyp_lemMeasureProofs.ndigits_measure_sufficient  b  n lemHyp lemFuel lemMeasureLe
```

The BEFORE obligation is FALSE: at `b = 1` no fuel is sufficient — every
frame adds 1 to whatever the frame below returns, so two fuels above the
measure disagree. Kernel-checked (`.tmp/plant/Counter.lean`, `lake env
lean`, exit 0): `ndigits_lemFuel 7 1 5 = 7 + 999`, `ndigits 1 5 = 6 +
999`, `¬ (ndigits_lemFuel 7 1 5 = ndigits 1 5)`, all by `decide` — a
counterexample to the unconditional statement at `lemFuel = 7 ≥ n + 1`.
The AFTER obligation is proved
(`Test_fuel_measure_hyp_lemMeasureProofs.ndigits_measure_sufficient`,
axioms `[propext, Quot.sound]`, §4), the hypothesis `2 ≤ b` excluding
exactly those inputs.

## 4. The proofs (the template, with the hypothesis)

`Test_fuel_measure_hyp_lemMeasureProofs.lean` — stability above the
measure by strong induction on the measured quantity generalizing the
two fuels, the hypothesis threaded through: `ndigits` (`lemNatDiv n b =
n / b` from `0 < b`, `Nat.div_lt_self` from `2 ≤ b` — the hypothesis is
used at exactly the two places the unconditional proof breaks);
`size_of` (`Ranked defs` gives `j < i` for every reference, so the
induction hypothesis applies through `List.foldl` via `foldl_add_congr`);
`down_steps` (`0 < step` makes `a - step < a`; the pair parameter is
destructured once in the obligation). The `count_list_bounded` proof
(`Test_contextual_keywords_lemMeasureProofs.lean`) is the (a)-flavoured
use: a caller-passed bound `k`, `List.length l ≤ k` turning `k + 1` into
a sufficient fuel. Kernel-only tactics, no option bump. Verbatim from
the build (`.tmp/gate2.log`):

```
info: Test_fuel_measure_hyp_lemMeasureProofs.lean:173:0: 'Test_fuel_measure_hyp_lemMeasureProofs.ndigits_measure_sufficient' depends on axioms: [propext, Quot.sound]
info: Test_fuel_measure_hyp_lemMeasureProofs.lean:174:0: 'Test_fuel_measure_hyp_lemMeasureProofs.size_of_measure_sufficient' depends on axioms: [propext, Quot.sound]
info: Test_fuel_measure_hyp_lemMeasureProofs.lean:175:0: 'Test_fuel_measure_hyp_lemMeasureProofs.down_steps_measure_sufficient' depends on axioms: [propext, Quot.sound]
```

## 5. Gates — verbatim

### 5.1 tests/comprehensive `make lean`, first full run (`.tmp/gate1.log`)

`make clean` then `make lean`: `=== Generation: 54 passed, 0 failed, 0
skipped ===`, `Build completed successfully (165 jobs).`, all compiled
legs OK, `OK: inv_fuel_measure_hyp.lem (7 artifacts byte-identical across
ocaml/hol/isa/coq)`, then the ONE expected failure of a first run:

```
  FAIL: no pin /home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-arc/fuel-parameter/tests/comprehensive/parity/expected/p_fuel_measure_hyp.out (record the OCaml reference with REBASELINE=1 and commit it)
make: *** [Makefile:35: lean-parity] Error 1
make lean  467.12s user 46.58s system 110% cpu 7:44.63 total
EXIT 2
```

The new probe's pin was then recorded ONCE from the OCaml reference,
verbatim (`REBASELINE=1 ./parity/run.sh p_fuel_measure_hyp`):

```
=== p_fuel_measure_hyp ===
  REBASELINED pin /home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-arc/fuel-parameter/tests/comprehensive/parity/expected/p_fuel_measure_hyp.out
  OK: parity (9 lines byte-identical to the OCaml reference; pin matches)
```

(the pin: `digits 10 0: 1`, `digits 10 255: 3`, `digits 2 255: 8`,
`digits 16 65535: 4`, `digits 2 deep: 27`, `steps (10,3): 4`, `steps
(0,1): 0`, `steps deep: 100000`, `uses_digits: 40`).

### 5.2 `make lean`, final head (`make clean` then `make lean`; `.tmp/gate2.log`)

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
make lean  570.81s user 48.50s system 108% cpu 9:32.74 total
EXIT 0
```

Derived counts: 97 × `OK (rejected as declared)` (the 11 new probes
among them), parity 26 OK / 6 both-fail / 4 XFAIL (the registered
`f_int_of_big_num`, `f_int32_overflow`, `p_str_bytes`, `p_str_escapes`
— the run's only `FAIL` lines), 8 invariance OK, 680 `PASS:` asserts —
among them `PASS: ndigits_ok`, `PASS: uses_ndigits_ok`, `PASS:
size_of_ok`, `PASS: down_steps_ok`, `PASS: ctx_kw_assuming_decl_ok`.

### 5.3 The missing-proofs plant still fires for the new shape (`.tmp/plant/`)

`ndigits_measure_sufficient` deleted from
`Test_fuel_measure_hyp_lemMeasureProofs.lean`, `lake build
Test_fuel_measure_hyp_auxiliary`, verbatim:

```
✖ [36/36] Building Test_fuel_measure_hyp_auxiliary (466ms)
error: Test_fuel_measure_hyp_auxiliary.lean:50:2: Unknown identifier `Test_fuel_measure_hyp_lemMeasureProofs.ndigits_measure_sufficient`
error: Lean exited with code 1
error: build failed
```

Restored: `Build completed successfully (36 jobs).`

### 5.4 The non-Prop hypothesis is a build failure (plant)

Scratch `test_plant_nonprop.lem` with ``assuming `n + 1` ``: generation
`EXIT 0` (accepted — a parameter is mentioned; the backend cannot type
Lean text), the module compiles, the auxiliary file does not, verbatim
(Lean 4.28.0, first error at the `lemHyp` binder, column 68):

```
Test_plant_nonprop_auxiliary.lean:30:68: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  HAdd Nat Nat (Sort ?u.5)
```

(TODO row 20 documents this as the designed limit.)

### 5.5 tests/nonlean-regress, lean-lib

`nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters,
byte-identical to golden)` — no rebaseline (no corpus file uses
`assuming`; the echo change is for the human targets only). `lean-lib`:
`lake build` green (capped; the library is UNCHANGED by this slice — its
23 `depends on axioms` lines as before — the first version of this sentence said "twelve"; pre-merge audit F3), `grep -rn "^axiom " lean-lib/
--include='*.lean'`: 0 hits.

### 5.6 OCaml AND Lean byte-identity of the cerberus tree

cerberus-lean primary @ `928aa1e76` (read-only: `LEM_SRC` = 86 files and
`LEM_SRC_LEAN` = 85 files obtained with `make --eval`, the Makefile's
flags `-wl ign -wl_rename warn -wl_pat_red err -wl_pat_exh warn
-cerberus_pp`, `-outdir` under `.tmp/`), baseline lem `d4ba548` rebuilt
from `git archive` (`.tmp/lem-base`), verbatim:

```
base ocaml exit 0 files 86
base lean exit 0 files 170
final ocaml exit 0 files 86
final lean exit 0 files 170
OCAML DIFF (cerberus frontend @ 928aa1e76, lem d4ba548 vs this lem) exit 0 lines 0
LEAN DIFF (same) exit 0 lines 0
```

`git -C cerberus-lean status --short` empty before and after. So both
renderer changes of §2.4 change no existing output.

## 6. The cerberus dry run (read-only; `.tmp/cerb`, scratch copy of `frontend/` + `lean_frontend/` @ `928aa1e76`)

### 6.1 Method

1. Copy patches, all in `.tmp/cerb`: `ctype_aux.lem` + 3 declares and
   `declare {lean} extra_import `CerbTagsWf``; `formatted.lem` + 1
   declare; a scratch seam `CerbTagsWf.lean` (the consumer-side
   VOCABULARY a hypothesis would name — `membersOf`, `refsOf`
   (by-value references: `Struct`/`Union0` tags, through `Array0` and
   `Atomic`), `Acyclic m := ∃ rank, ∀ (tag, (_, d)) ∈ fmapElements m, ∀
   c ∈ membersOf d, ∀ t ∈ refsOf c, rank t < rank tag`, `tagCount`,
   `defsSize`, `envBound m ty := (tagCount m + 1) * (ctype.lemSize ty +
   defsSize m + 1)`, `paramsBound`) and `CerbMemHypShape.lean` (§6.4).
2. Generation with this lem: `lean-after exit 0 files 170`; tree
   without vs with the 4 declares: 7 modules differ (`Ctype_aux`,
   `Ctype_aux_auxiliary`, `Formatted`, `Formatted_auxiliary`, and the
   callers `Core_aux`, `Core_aux_auxiliary`, `Core_reduction`);
   `[LemFuel]` binders 251 → 240 (derived; `Ctype_aux` 4 → 0, `Formatted`
   19 → 17, `Core_aux` 7 → 4, `Core_reduction` 6 → 5, `Core_aux_auxiliary`
   1 → 0).
3. Build (Lean 4.32.2, `CERB_MEM_MAX=16G`, cerberus's `lakefile.toml`
   with LemLib re-pointed to a scratch COPY of this tree's `lean-lib` —
   the shared-`.lake` hazard of the fuel-measure record §6.1 —,
   `generated/` = the new tree + the 35 hand-written files + the two
   scratch seams, the two auxiliary shells' obligations turned into
   `example <binders> : Prop := (<conclusion>)` and their (non-existent)
   proofs imports dropped — so the STATEMENTS elaborate with no proof and
   no `sorry` anywhere): `lake build Ctype_aux_auxiliary
   Formatted_auxiliary CerbMemHypShape`, verbatim (`.tmp/cerb/build-dryrun.log`):

```
⚠ [10/91] Built LemLib (1.2s)
✔ [59/91] Built CerbTagsWf (182ms)
⚠ [74/91] Built Ctype_aux (969ms)
⚠ [75/91] Built Ctype_aux_auxiliary (495ms)
⚠ [77/91] Built CerbMem (3.0s)
⚠ [79/91] Built CerbMemHypShape (475ms)
⚠ [90/91] Built Formatted (1.1s)
⚠ [91/91] Built Formatted_auxiliary (230ms)
Build completed successfully (91 jobs).
EXIT 0
```

(0 `error` lines; the ⚠ are the pre-existing derived-comparison /
unused-variable warnings.)

### 6.2 A finding on the way: lem's rename pass vs the declare's parameter names

The first generation refused `are_compatible_params_aux` with, verbatim:

```
Error: Lean backend: the measure hypothesis of are_compatible_params_aux0 (`CerbTagsWf.Acyclic env.1 ∧ CerbTagsWf.Acyclic env.2`) mentions none of its parameters env1, acc, lemTail (FH-vacuous: …)
```

The `.lem` names the parameter `env`; lem's rename pass (`-wl_rename
warn`) makes it `env1` before the backend sees it, so `env` is not a
parameter — and `env.1` PASSED as a qualified global, leaving no parameter
mentioned. Two consequences, both in this slice: the projection refusal
(§2.4 item 2) so this is reported as what it is, and the manual's note
that the parameter names are the worker's and the refusal lists them.
The declares in the copy use `env1`.

### 6.3 The table (the 13 candidate rows of `scripts/fuel_forms_pending.txt`)

Columns: proposed measure and hypothesis (over the Lean worker's
parameters), accepted by this lem (`✓` = generates, obligation shell
elaborates in §6.1; `hand` = no lem declare applies — the seam is
hand-written; `—` = not proposed, reason given). Measures and
hypotheses are PROPOSALS [AGENT]; the sufficiency PROOFS are the
cerberus half's, and for the mutual trio the joint bound is the proof's
business (the measures are acceptance witnesses).

| Row | Function | Measure | Hypothesis | Accepted? |
|---|---|---|---|---|
| 1 | `CerbMem.sizeofCtype_lemFuel` | `CerbTagsWf.envBound ambient cty` | `CerbTagsWf.Acyclic ambient` | hand (§6.4: statement elaborates) |
| 2 | `CerbMem.alignofCtype_lemFuel` | `envBound ambient cty` | `Acyclic ambient` | hand |
| 3 | `CerbMem.offsetsof_lemFuel` | `envBound`-style over the tag's members: `(tagCount tagDefs + 1) * (defsSize tagDefs + 1)` | `Acyclic tagDefs` (the explicit `tagDefs` argument; `ambient` is the alignment oracle's) | hand |
| 4 | `CerbMem.offsetsofMembers_lemFuel` | `(tagCount tagDefs + 1) * (Σ ctype.lemSize over members + defsSize tagDefs + 1)` | `Acyclic tagDefs` | hand |
| 5 | `CerbMem.memberAlign_lemFuel` | `envBound tagDefs ty` (+1 for the `_Alignas` type arm) | `Acyclic tagDefs` | hand |
| 6 | `CerbMem.reconstructValue_lemFuel` | `envBound ambient cty` (its recursion is on the ctype being reconstructed, through member types read from `tagDefs`) | `Acyclic ambient` | hand |
| 7 | `are_compatible_aux_lemFuel` (ctype_aux) | `CerbTagsWf.envBound p.1 p0.2 + CerbTagsWf.envBound p.2 p1.2 + 1` | `CerbTagsWf.Acyclic p.1 ∧ CerbTagsWf.Acyclic p.2` | ✓ |
| 8 | `are_compatible_params_aux0_lemFuel` | `CerbTagsWf.paramsBound env1.1 lemTail.1 + CerbTagsWf.paramsBound env1.2 lemTail.2 + 1` | `CerbTagsWf.Acyclic env1.1 ∧ CerbTagsWf.Acyclic env1.2` | ✓ |
| 9 | `are_compatible_params0_lemFuel` | `CerbTagsWf.paramsBound env1.1 params1 + CerbTagsWf.paramsBound env1.2 params2 + 1` | `CerbTagsWf.Acyclic env1.1 ∧ CerbTagsWf.Acyclic env1.2` | ✓ |
| 10 | `hack_lemFuel` (driver) | — | — | — : a step-until-value evaluation loop on the REWRITTEN pexpr; no hypothesis on the parameters (`core_extern env mem_st core_file concur_sym_map pexpr`) bounds the number of steps short of "the evaluation of `pexpr` terminates within k steps", and `k` is not a parameter (a measure over the parameters would have to compute the loop). Honestly: no. Stays P (D-C2-4: a body change or an ND-monad move). |
| 11 | `many_lemFuel` (monadic_parsing) | — | — | — : the recursion depth is the INPUT's length, which is inside the `parserM` lambda — the only parameter is the parser `p`, a function; no Nat measure and no Prop over `p` alone bounds the depth ("`p` consumes input" is a fact about `p`'s behaviour on every input, and even then the bound is the input's length, not a function of `p`). Stays P (D-C2-5). |
| 12 | `many1_lemFuel` | — | — | — : sibling of 11 (mutual; all-or-none). |
| 13 | `showNonNegativeWithBasis_aux_lemFuel` (formatted) | `n + 1` | `2 ≤ b` | ✓ — D-C2-6's "provable if `lemNatDiv n 0` were transparent" is now moot: with `2 ≤ b` the `b = 0` arm is excluded and `lemNatDiv n b = n / b` (the suite's `ndigits` is this row's shape; proof template §4) |

Tally (derived): 4 lem rows accepted and generated (3 tag-lookup + the
basis), 6 hand-written seams with the statement shape shown to
elaborate, 3 not proposed (`hack`, `many`, `many1`) — 13. `to_pure`/
`to_pures` are not this mechanism's customers (opaque-arg; D-C2-3).

Generated wrappers (verbatim heads, `lean-after`):

```lean
def showNonNegativeWithBasis_aux ( acc : List (Char)) ( useUpper : Bool) ( b : Nat) ( n : Nat) : List (Char) := showNonNegativeWithBasis_aux_lemFuel (n + 1)  acc  useUpper  b  n
def are_compatible_aux (p : (Fmap (sym) ((CerbLocation.Loc ×tag_definition)) ×Fmap (sym) ((CerbLocation.Loc ×tag_definition)))) (p0 : (qualifiers ×ctype)) (p1 : (qualifiers ×ctype)) : Bool := are_compatible_aux_lemFuel (CerbTagsWf.envBound p.1 p0.2 + CerbTagsWf.envBound p.2 p1.2 + 1) p p0 p1
```

Generated obligations (verbatim statements):

```lean
theorem showNonNegativeWithBasis_aux_measure_sufficient ( acc : List (Char)) ( useUpper : Bool) ( b : Nat) ( n : Nat) (lemHyp : (2 ≤ b)) (lemFuel : Nat) (lemMeasureLe : (n + 1) ≤ lemFuel) :
    showNonNegativeWithBasis_aux_lemFuel lemFuel  acc  useUpper  b  n = showNonNegativeWithBasis_aux  acc  useUpper  b  n :=
theorem are_compatible_aux_measure_sufficient (p : (Fmap (sym) ((CerbLocation.Loc ×tag_definition)) ×Fmap (sym) ((CerbLocation.Loc ×tag_definition)))) (p0 : (qualifiers ×ctype)) (p1 : (qualifiers ×ctype)) (lemHyp : (CerbTagsWf.Acyclic p.1 ∧ CerbTagsWf.Acyclic p.2)) (lemFuel : Nat) (lemMeasureLe : (CerbTagsWf.envBound p.1 p0.2 + CerbTagsWf.envBound p.2 p1.2 + 1) ≤ lemFuel) :
    are_compatible_aux_lemFuel lemFuel p p0 p1 = are_compatible_aux p p0 p1 :=
```

### 6.4 The hand-written seams (rows 1–6)

The lem declare does not apply to `CerbMem.lean`'s hand-written workers.
The design for them: the SAME obligation statement shape, written by hand
— parameters, `(lemHyp : H)`, `(lemFuel : Nat)`, `(lemMeasureLe : μ ≤
lemFuel)`, `worker lemFuel … = wrapper …` — with the wrapper turned into
the fuel-free measured form (`def sizeofCtype (ambient) (cty) :=
sizeofCtype_lemFuel (envBound ambient cty) ambient ambient cty`, replacing
today's `[LemFuel]` + `LemFuel.fuel`), so the consumer gate's shape check
(the `lemHyp` binder) is the only thing that needs to know. Elaborated
witness (`CerbMemHypShape.lean`, built in §6.1 — statement only):

```lean
def sizeofCtype (ambient : CerbTags.TagDefsMap) (cty : ctype) : Nat :=
  CerbMem.sizeofCtype_lemFuel (CerbTagsWf.envBound ambient cty) ambient ambient cty
example (ambient : CerbTags.TagDefsMap) (cty : ctype) (lemHyp : (CerbTagsWf.Acyclic ambient)) (lemFuel : Nat)
    (lemMeasureLe : (CerbTagsWf.envBound ambient cty) ≤ lemFuel) : Prop :=
  CerbMem.sizeofCtype_lemFuel lemFuel ambient ambient cty = sizeofCtype ambient cty
```

Consequence for callers: today's ambient callers of the five layout
functions (`memValueToBytes` keeps `[LemFuel]` "for the ambient layout
oracle", `CerbMem_lemMeasureProofs.lean`) lose that binder once the
seams are measured — the fuel-parameter arc's work list item 2, now with
a hypothesis.

### 6.5 What the dry run does NOT check

The four obligation PROOFS and the six seam proofs (the cerberus half's
— no `sorry` was written, even in scratch; the shells were elaborated as
Props); whether `envBound` is the right bound (the proposal's shape is
"passes each tag at most once per path, descends structurally between
lookups" — the proof will say); the runtime (differential lanes); the
gate's classification of the new shape (§2.2 says it already counts as
MEASURED; distinguishing "under H" is the consumer's policy choice).
The cerberus `.lem` and `lean_frontend/` were not edited.

## 7. TODO rows

- 20 (new): a non-Prop hypothesis is a build error, not a generation
  refusal — designed limit. —.
- 21 (new): `sizeOf` refused in a hypothesis for uniformity only. S.
- 22 (new): the hypothesis-carrying hand-written seams (cerberus half). —.
- 18 (note): the consolidation's TERMINATION family gains the
  `[assuming `H`]` clause.

## 8. Decisions for the operator

1. **The gate's reading of the conditional form.** The consumer's
   `FuelFormsTool` classifies the hypothesis-carrying obligation MEASURED
   today (§2.2). Whether the register should distinguish "MEASURED under
   H" (report `hyp=…`, keep a list of the hypotheses in force) is a
   cerberus-half policy; the mark (`lemHyp` before `lemFuel`) is there.
2. **`sizeOf` in a hypothesis** (TODO 21): refused for one vocabulary;
   lift if wanted.
3. **`hack`, `many`, `many1`** stay P by this mechanism (table rows
   10–12): no hypothesis on the parameters bounds them. Options are the
   C2 record's D-C2-4/5 (a body change; the ND monad).
4. **The dry run's `Acyclic`-as-a-rank and `envBound`** are proposals
   for the cerberus half's `CerbTagsWf`-like module; the frontend's
   invariant that tag environments are acyclic is the consumer's to
   state (a decidable version — a rank computed by a bounded traversal —
   would let the differential lanes check it at load time).

## 9. Not done, and why

- The cerberus-side proofs, seams and gate changes (by charter: the
  dry run is a read-only copy; §6.5).
- A generation-time Prop heuristic (TODO 20): the build is the gate.
- `.tmp/` (the baseline lem, the cerberus copies and build, the plants,
  the logs) is ephemeral and deleted at slice end; everything load-bearing
  is quoted above.

## 10. Audit response (pre-merge audit `2026-09-05_measure-hypothesis-audit-premerge.md` @ `05a533f`, verdict MERGEABLE; F1 MAJOR-by-letter, F4 MINOR code, F2/F3 errata, N11)

One commit on `arc/measure-hypothesis`. Each item, what changed, and the
evidence (verbatim from this worktree, `.tmp/build5.log`,
`.tmp/gate3.log`, `.tmp/nonlean3.log`, `.tmp/plant/f4/`).

- **F4 (code, one line + probe).** `lean_is_letter_like` now carries the
  three entries the first table omitted — Latin-1 supplement `0x00C0–0x00FF`
  minus `×` (`0x00D7`) and `÷` (`0x00F7`), Latin Extended-A `0x0100–0x017F`,
  and `U+2C7C` — transcribed from `Init/Meta/Defs.lean` (4.28.0 :100–118,
  4.32.2 :108–118, identical). The auditor's p30 is now the negative probe
  `neg_fuel_measure_hyp_latin1.lem` (``assuming `2 ≤ ñ ∧ 2 ≤ b` ``),
  refused at generation, verbatim:
  ```
    Error: Lean backend: free variable `ñ` in the measure hypothesis (`assuming`) of ndigits (FH-free: a measure or hypothesis mentions only the function's parameters — here b, n — and QUALIFIED Lean names such as `List.length xs`, `Ns.size x` or `Ns.WellFormed env`, or `lemSize x` for the derived size of a parameter's inductive type; Lean's global namespace is not visible at generation, so an unqualified name that is not a parameter is refused)
  EXIT 1
  ```
  and the auditor's p31 (``assuming `2 ≤ bⱼ` ``, `.tmp/plant/f4/p31.lem`)
  is now read as ONE identifier and refused: ``free variable `bⱼ` ``,
  `p31 EXIT 1`; the control (`2 ≤ b`, `test_fuel_measure_hyp.lem`)
  generates (`EXIT 0`). §2.4 item 1 now says "a table transcribed from"
  Lean's predicates, lists every range, and names the residual
  divergence (subscripts may START an identifier here). `make build-lem`
  `BUILD EXIT 0` (the grammar is untouched: no ocamlyacc re-run).
- **F1 (no lem code change; record, manual, DESIGN, TODO row 23).**
  §2.3's "what the syntactic rules do not catch" now names the
  contradictory direction and its consequence — a vacuously provable
  obligation shipping the fuel-free wrapper with the MEASURED mark;
  satisfiability of a Lean Prop is undecidable at generation, the
  literal-only vacuity check is a token-level speedbump — and states the
  CONSUMER-SIDE REQUIREMENT (a requirement of the cerberus half, not an
  optional policy; the first version of §2.2/§8.1 said "policy choice"):
  (i) the fuel-forms gate reports `hyp=<H>` for every MEASURED row whose
  obligation has the `lemHyp` binder, read by NAME immediately before
  `lemFuel`; (ii) a reviewed hypothesis register — every hypothesis in
  force named, its frontend invariant cited (for `Acyclic`: the audit §5
  — `cabs_to_ail.lem` `check_members` refuses function-typed and
  incomplete members, `AilTypesAux.is_complete` makes a by-value
  `Struct`/`Union` member complete only when its tag is already defined,
  so definition order is a rank; pointers break the recursion). The
  manual's paragraph, the DESIGN vocabulary row and TODO row 23 say the
  same; §8 item 1 below is superseded accordingly. The manual also gains
  the auditor's N2 line (a hypothesis with its own binders is refused as a
  free variable — write a NAMED consumer-side predicate).
- **F2.** TODO row 20 now quotes the actual failure —
  `error(lean.synthInstanceFailed): failed to synthesize instance of type
  class HAdd Nat Nat (Sort ?u.5)` — and records that its first version
  said `type expected`.
- **F3.** §5.5 now says 23 `depends on axioms` lines (the first version
  said "twelve"); lean-lib is unchanged by the slice.
- **N11.** `Test_contextual_keywords_lemMeasureProofs.lean` ends with
  `#print axioms` for both `count_list_measured_measure_sufficient` and
  `count_list_bounded_measure_sufficient`; verbatim from the build below.

Gates on this tree (clean `make clean` then `make lean`, `.tmp/gate3.log`;
`tests/nonlean-regress/run.sh`, `.tmp/nonlean3.log`), verbatim:

```
=== Generation: 54 passed, 0 failed, 0 skipped ===
Build completed successfully (165 jobs).
  OK (rejected as declared): negative/neg_fuel_measure_hyp_latin1.lem
  OK: inv_fuel_measure_hyp.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
=== p_fuel_measure_hyp ===
  OK: parity (9 lines byte-identical to the OCaml reference; pin matches)
  OK: 10 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
  OK: 254 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make lean  525.72s user 46.92s system 110% cpu 8:39.29 total
EXIT 0
```
```
info: Test_contextual_keywords_lemMeasureProofs.lean:62:0: 'Test_contextual_keywords_lemMeasureProofs.count_list_measured_measure_sufficient' depends on axioms: [propext,
 Quot.sound]
info: Test_contextual_keywords_lemMeasureProofs.lean:63:0: 'Test_contextual_keywords_lemMeasureProofs.count_list_bounded_measure_sufficient' depends on axioms: [propext,
 Quot.sound]
```
```
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
EXIT 0
```
Derived: 98 × `OK (rejected as declared)` (97 + the F4 probe), parity 26
OK / 6 both-fail / 4 XFAIL (the four registered — the run's only `FAIL`
lines), 8 invariance OK, 680 `PASS:` asserts. The backend change touches
one table (`lean_is_letter_like`); the grammar is untouched.

**§8 item 1, superseded by F1:** the gate's `hyp=<H>` report and the
reviewed hypothesis register are REQUIRED of the cerberus half before its
first `assuming` row, not a policy choice.


## 11. Orchestrator boundary review [AGENT, orchestrator, 2026-09-05]

Independent re-verification, lem rebuilt from source in this worktree, at
`906ac21` (the slice) and at `e58151f` (audit response `7963352` + the
audit document `05a533f` cherry-picked). Final run, verbatim:

```
Lem e58151f
=== Generation: 54 passed, 0 failed, 0 skipped ===
  OK: 254 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make-lean-rc=0
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
```

(lean-lib `Build completed successfully (39 jobs)`, zero axioms, the four
registered XFAILs only.) Pre-merge audit
`2026-09-05_measure-hypothesis-audit-premerge.md`: verdict MERGEABLE, but
F1 graded MAJOR "by the scope's letter" (contradictory hypotheses pass the
token-level vacuity check; disposition: undecidable at generation; a
cerberus-half REQUIREMENT — `hyp=<H>` reporting + a reviewed hypothesis
register — recorded in §10/TODO row 23). The operator's overnight pre-sign
for this branch was conditional on "no MAJOR"; under a fail-closed reading
the orchestrator did NOT merge under the pre-sign — the branch is held for
the operator's explicit merge ask [AGENT decision, logged]. Cerberus OCaml
+ Lean byte identity (86/86, 170/170) verified by the auditor.
