# Pre-merge audit — `arc/structural-declare` (structural declare + fuel-measure declare)

Auditor [AGENT], 2026-09-04. Range audited: lem-lean `9ba8970` (mainline
`mdd/lean-backend`) → `d8a17e3` (7 commits: `d8bbb4e`, `3c1846b`,
`76b76da`, `020df26`, `005f9bb`, `af5d431`, `d8a17e3`). Audit worktree:
a fresh checkout of `d8a17e3` (`worktrees/lem-lean-audit/structural-measure-premerge`,
branch `audit/structural-measure-premerge`); everything below was
built and run THERE (`make`, `tests/comprehensive make lean`,
`tests/nonlean-regress/run.sh`, `lean-lib lake build`, probes and
plants under `.tmp/`). Nothing in the arc worktree, `deps/`, or
cerberus-lean was modified. Every quoted output is verbatim; tallies
marked "derived" are derived. Budget used ≈ 1 h 20 min; no run exceeded
10 min (longest: `make lean` 5:10).

## Verdict: MERGE-WITH-FIXES

No MAJOR finding. The OCaml output is byte-identical (cerberus tree
86/86 files, `diff -r` empty; the non-Lean net is green with no
rebaseline in the fuel-measure slice and a human/echo-only rebaseline
in D4); no non-Lean emitter changed; the well-founded fallback is
impossible in emitted code; every negative probe refuses with its
reason; the obligation shell fails the build when the proof module or
a theorem of the stated type is missing (four plants). Four MINOR
findings should land before the merge (one is a one-line fail-closed
tightening of a documented rule; the others are a record tally, a
probe that passes for the wrong reason, and a suite gap the consumer's
gates already cover); the rest are NOTEs.

## Findings

### MINOR

**M1 — FM-ambient / FM-sizeOf are checked on the HEAD token only; a
`_root_.` prefix evades both at generation.** `lean_render_measure`
(`src/lean_backend.ml`) classifies an identifier by the text before its
first `.`; `_root_` is neither `LemFuel`, `sizeOf`, `lemFuel` nor
`_lem…`, and has a non-empty tail, so it is accepted as a qualified
global. Probe `m2_root_ambient.lem` (a measured function whose body
passes the ambient on, so its wrapper carries `[LemFuel]`):

```
declare {lean} fuel_measure val mouter = `_root_.LemFuel.fuel + 0 * List.length l`
```
generation: `lem exit 0`; generated wrapper, verbatim:
```
def mouter [LemFuel] ( l : List (Nat)) : Nat := mouter_lemFuel (_root_.LemFuel.fuel + 0 * List.length l)  l
```
Lean 4.28.0 (`.tmp/probes/pkg`): `✔ [33/33] Built M2_root_ambient` — and
the wrapper is fuel-DEPENDENT, kernel-checked (`CheckM2.lean`, built):
```
example : @mouter ⟨0⟩ [1] = 997 := by decide
example : @mouter ⟨5⟩ [1] = 0 := by decide
example : @mouter ⟨0⟩ [1] ≠ @mouter ⟨5⟩ [1] := by decide
```
The generated obligation `LemFuel.fuel + 0 * … ≤ lemFuel → mouter_lemFuel
lemFuel l = mouter l` is therefore FALSE and unprovable — the kernel
backstop holds, so this is not fail-open — but the manual states
"`LemFuel` anywhere in a measure is refused" and the code does not
implement that. Likewise `_root_.sizeOf l` (`m3_root_sizeof.lem`) passes
generation (`lem exit 0`, wrapper `mlen_lemFuel (_root_.sizeOf l)  l`) and
is caught only by Lean (`error: M3_root_sizeof.lean:32:50: Unknown
identifier `_root_.sizeOf``). The plain forms are refused as documented
(`m9`: `Error: Lean backend: the fuel measure of mouter mentions
`LemFuel.fuel` (FM-ambient …)`; suite `neg_fuel_measure_sizeof`).
*Fix:* refuse a `_root_` head outright (a qualified name never needs
it) and apply the `LemFuel`/`sizeOf`/`SizeOf` tests to every dotted
component, not the head only; add `neg_fuel_measure_root_ambient`.

**M2 — a `sorry` in the hand-written proofs module passes lem-lean's
suite.** Plants in `tests/comprehensive/lean-test` (`.tmp/plants.log`,
`lake build Test_fuel_measure_auxiliary`, each restored by `git
checkout` afterwards; `git status` clean after each):
```
=== baseline
Build completed successfully (35 jobs).
exit=0
=== P1: mlen theorem missing (renamed)
error: Test_fuel_measure_lemMeasureProofs.lean:199:14: Unknown constant `Test_fuel_measure_lemMeasureProofs.mlen_measure_sufficient`
exit=1
=== P2: wrong statement (hypothesis +2 instead of +1)
error: Test_fuel_measure_lemMeasureProofs.lean:48:44: Application type mismatch: The argument
exit=1
=== P2b: proofs module theorem well-typed but of the WRONG type (conclusion mlen l = mlen l)
error: Test_fuel_measure_auxiliary.lean:55:2: Type mismatch
exit=1
=== P3: proof replaced by sorry
Build completed successfully (35 jobs).
exit=0
=== P4: proofs module file removed
error: Test_fuel_measure_auxiliary.lean: bad import 'Test_fuel_measure_lemMeasureProofs'
exit=1
```
So "the build fails without it" (record §2.2, manual, DESIGN) is true
for a missing module, a missing theorem and a theorem of another type
(P1/P2/P2b/P4 — the P1 plant reproduces the record's quote exactly), but
NOT for `sorry` (or an `axiom`): P3 is green. lem-lean's suite has no
`sorry`/`axiom` scan (`grep -rn "sorry\|axiom" tests/comprehensive/Makefile
tests/comprehensive/*.sh tests/comprehensive/parity/run.sh` → nothing).
The consumer IS covered: cerberus's `check_sorry_token.sh` and
`check_theorem_axioms.sh` (VALIDATION.md rows) scan the hand-written
seams, which is where `<Module>_lemMeasureProofs.lean` would live.
*Fix:* a vacuity-guarded `sorry`/`axiom` token scan over
`lean-test/*_lemMeasureProofs.lean` and `parity/probes/*.proofs.lean` in
the suite (the `#print axioms` lines are printed, not asserted), and
qualify the sentence to "a missing or mistyped theorem fails the build;
`sorry`/`axiom` are the consumer's axiom gate's job".

**M3 — the dry-run tally 38/11/16/2 does not match its own table.**
Recount of `2026-09-04_fuel-measure-record.md` §6.2 by class column
(derived, awk over the 67 rows): MEASURED 38; `(B)` 10 (rows 2, 41–44,
48, 49, 56–58); `RESIDUE/(B)` 2 (rows 3, 4: `many`/`many1`); `RESIDUE`
(incl. the point-free variants) 15; `SAME-MODULE` 2. The tally text says
"(B) 11" while listing exactly ten names and "many/many1 counted under
residue", and "RESIDUE 16" while its own breakdown reads "tag lookup 5"
(six names: `zeros_aux`, `are_compatible_aux` + 2 siblings, `mkUnspec`,
`simplify_integer_value_base`), "point-free tail 7" (six names:
`one_step_unseq_aux`, `get_ctx` + `get_ctx_unseq_aux`, `are_compatible` +
2 siblings), 1, 1, 1, 2 — labels sum to 17, names to 17. Consistent
readings: 38/10/17/2 (many/many1 residue) or 38/12/15/2 (many/many1 (B));
either sums to 67. *Fix:* correct the tally and the two sub-labels; the
commit message of `d8a17e3` and the record's title carry the wrong
numbers too.

**M4 — `neg_structural_shadow` passes for the wrong reason.** Its
self-call is `bad (xs :: [])` — a non-variable argument — and its
`EXPECT` is "the argument is not a variable"; the shadowing path of the
analysis (`Fun … -> walk (remove …)`) is never exercised by the suite.
A real shadowing probe (`.tmp/probes/s1_shadow_real.lem`: `List.foldl
(fun acc xs -> acc + bad xs) 0 [xs]`) IS refused by the right rule,
verbatim:
```
Error: Lean backend: 'declare {lean} structural val' refused — no parameter of bad is passed a strict structural subterm (a variable bound by a constructor pattern on that parameter) at every recursive call:
  parameter l: at the self-call File "../../s1_shadow_real.lem", line 7, character 50 to line 7, character 55, the argument `xs` is a variable that is not bound by a constructor pattern on that parameter (bound by a lambda or let, or by a match on a computed scrutinee — …)
```
*Fix:* make the probe's call `bad xs` and its EXPECT "not bound by a
constructor pattern".

**M5 (cerberus half, not this branch) — lakefile roots are not
mechanically synced with the generated modules.** Today every generated
`_auxiliary` is a root in cerberus's `lakefile.toml` (derived: 85 roots
= 85 `generated/*_auxiliary.lean`, `comm` empty both ways; all 108 non-aux
modules rooted too), so the obligation cannot be skipped in the tree as
it stands — NOT the MAJOR the audit brief anticipated. But nothing
checks it (`tools/check_handwritten_sync.sh`, `scripts/*.sh`: no root
census), and plant P5 shows the failure mode: with
`Test_fuel_measure_auxiliary` and the proofs module dropped from the
suite's `lakefile.lean`, `lake build` (default target) is green —
`Build completed successfully (149 jobs).` `exit=0` — with the
obligations unbuilt. *Fix (cerberus half):* a gate that every
`generated/*.lean` is a root (fail on drift), alongside the seam list's
item 3.

### NOTE

**N1 — constant measures disguised as parameter-mentioning pass FM-const
by design; the theorem is the gate.** `l.length - l.length + 5`
(`m1`) and `Nat.succ Nat.zero + 0 * List.length l` (`m5`): `lem exit 0`;
wrappers `mlen_lemFuel (l.length - l.length + 5)  l` / `mlen_lemFuel
(Nat.succ Nat.zero + 0 * List.length l)  l`; the no-numerals gate is
green on them (the F3 refinement is deliberate, record §5.4). Their
obligations are FALSE, kernel-checked (`CheckM1.lean`, built):
`example : mlen_lemFuel 100 [1,2,3,4,5,6] ≠ mlen [1,2,3,4,5,6] := by
decide` — so they are unprovable and the function cannot ship. This is
the record's own position ("numerals INSIDE a measure … certified by the
obligation"); the manual should say in one sentence that the syntactic
rules are speedbumps and the theorem is the certificate.

**N2 — the obligation's statement: what it is and is not.** Auditor's
assessment: `∀ lemFuel ≥ μ x, f_lemFuel lemFuel x = f x` with `f x =
f_lemFuel (μ x) x` by `rfl` is exactly fuel-irrelevance above the
measure — for any `n, m ≥ μ x`, `W n x = W (μ x) x = W m x` — which is
what the consumer's `∀ fuel`-theorems need, and it is the operator's
reading ("the fuel simply doesn't matter, so it's no longer a
parameter"). It cannot hold vacuously (the hypothesis is satisfiable at
`lemFuel := μ x`) and cannot hold "trivially because `W` ignores its
counter" (a fuel'd worker always matches on it). It is NOT "exhaustion
unreachable at μ": a divergent `f x = f x` with sentinel `999` has `W n
x = 999` for every `n`, so `f_measure_sufficient` is provable for ANY
measure, and a sentinel-masking body has the same gap. The record §2.2
says this (the "residual gap", operational, seen by the loud
`fuelExhausted` convention and the differential lanes) and the manual
repeats it; the generated comment's phrase "the measure is a
sufficient fuel" and the theorem's name overclaim slightly — "the worker
is fuel-STABLE at the measure" is the precise claim. Wording only.

**N3 — fixpoint change verified.** `lean_fuel_is_ambient` = fuel'd ∧ ¬
measured in `lean_fuel_prepass`, `exp_needs_fuel` and the block's
ambient-reach test; consumer chain plant `m4_chain.lem` (`c1 = mlen l +
1`, `c2 = c1 l * 2`, `c3 = List.map c2 l`): generated `def  c1 (l : List
Nat) : Nat := mlen l + 1`, `def  c2 …`, `def  c3 …` — no binder;
`CheckM4.lean` (built): `example : List Nat → Nat := c1`, `… := c2`,
`example : List (List Nat) → List Nat := c3`, `example : c3 [[1],[1,2]] =
[4, 6] := by decide`. The suite's `mouter` (body passes the ambient on)
keeps `[LemFuel]`; the prepass/ambient-reach agreement is an internal
error if violated — read, not plantable from lem.

**N4 — structural analysis vs Lean's checker, adversarial set.** Refused
at generation, each with the parameter/call/reason (verbatim in
`.tmp/probes/out/*/gen.log`): real shadowing (`s1`, M4 above); n+k on
nat (`s2`: "the argument `m0` is a variable that is not bound by a
constructor pattern" — the n+k is desugared BEFORE the analysis: the
no-declare render is `partial def  tri  (n : Nat)  : Nat :=   if (n ==
0) then   0  else (let m0  := n -   1; n  +  tri  m0)`, so `bind_pat`'s
`P_num_add` branch is dead on this backend — harmless); a recursive
record (`s3`: record pattern → projections, refused via the mutual-block
message); a mutual cross-call passing the parameter itself (`s5`: "a
call to a mutual sibling … has no structural position consistent with
the block" — Lean's `brecOn` cannot use a same-argument call either);
`fuel` + `structural` (`s9`: ST-fuel); non-recursive (`s10`: ST-nonrec).
`s2` is the one "Lean's checker would accept, the analysis refuses"
case (the record names it). Designated by the analysis AND accepted by
Lean 4.28.0 (each `✔ Built`, kernel `decide`/`rfl` in `CheckS*.lean`):
`s4` let-alias of the subterm (`let ys := xs; 1 + f ys`,
`termination_by structural l`), `s6` a parameter named like a top-level
constant (lem's avoid renames it `len1` in binder AND clause), `s7` a
Lean-keyword parameter (`def1`), `s8` a call inside a lambda on an
outer strict subterm, `s11` a `(l, k)` tuple scrutinee bound
component-wise (`match l,  k with … termination_by structural l`). No
"analysis designates, Lean refuses" case found beyond the record's own
(the record pattern, already a probe).

**N5 — WF fallback impossible in emitted code.** All `termination_by`
lines in generated suite + probe files (derived, `grep | uniq -c`): `304
termination_by structural cmpx_` (the pre-existing derived comparison),
`15 … structural l`, `2 … ts`, `2 … t`, `2 … l1`, `1 … len1`, `1 …
def1`; the only non-`structural` hits are the hand-written
`TestFuelMeasureImpl.lean` (`termination_by structural t => t`) and
identifiers/comments in `Test_keywords.lean`/`Test_structural.lean`; zero
`decreasing_by`.

**N6 — D4 verified.** Lean 4.32.2 (cerberus's toolchain), `#eval`,
verbatim: `Int32.ofInt (-1)` → `-1`; `Int32.ofInt 2147483648` →
`-2147483648`; `Int32.ofInt (-2147483649)` → `2147483647`; `Int32.ofInt
4294967296` → `0`; `Int32.ofNat 4294967297` → `1`; `Int64.ofInt
9223372036854775808` → `-9223372036854775808`; `Int64.ofNat
18446744073709551617` → `1`; `example : Int32.ofInt 2147483648 =
Int32.ofInt (-2147483648) := by decide` and `(Int32.ofInt 4294967297).toInt
= 1 := by decide` accepted — the modular `word_of_int`/`n2w` reading
(`library/num.lem:2378-2396`, `:2453-2470`, the isabelle/hol reps read).
Suite: `=== f_int32_overflow ===` / `ocaml: failed as expected (exit 2):
Fatal error: exception Failure("int32_of_big_int")` / `FAIL: failure
probe, but the Lean binary SUCCEEDED (exit 0) …` / `XFAIL (expected,
registered): RULED OCaml-target deviation ([USER 2026-09-04] …`; `=== p_int_wrap
===` / `OK: parity (42 lines byte-identical to the OCaml reference; pin
matches)`. `…Exact` references remaining (`grep -rn "OfIntegerExact\|OfNaturalExact"`
over `*.lean *.lem *.ml *.sh`): only the historical mention in
`f_int32_overflow.lem`'s comment. Wording nit: `expected_failures.txt`
says the OCaml target "raises Z.Overflow"; the binary's text is
`Failure("int32_of_big_int")` (nat_big_num's wrapper).

**N7 — golden rebaseline (27 rows) verified.** `diff <(LC_ALL=C sort
9ba8970:golden.sha256) <(LC_ALL=C sort golden.sha256)` restricted to
`ocaml`/`hol`/`isa`/`coq` rows: EMPTY. Changed rows by emitter (derived,
`-`/`+` lines): `backends/tex_all` 40, `lib/tex_all` 4, `lib/tex` 4,
`lib/lem` 2, `lib/ident.stdout` 2, `lib/html` 2 = 54 lines = 27 pairs,
matching the record §7.5 exactly.

**N8 — the `sizeOf` finding reproduced on Lean 4.32.2** with a different
message: `#eval sizeOf [1,2]` → `error: Failed to find LCNF signature
for List._sizeOf_inst` (the record quotes 4.28.0's `has no executable
code`). Same fact; the manual states it.

**N9 — the `liftAction` `_zero` fix.** Pre-fix shape (`020df26`):
`theorem <w>_zero … : <w> 0 <args> = <sentinel> := rfl` with no
ascription; `d8a17e3` adds `tail_ascription` when `npats < arity` (not
under supply), wrapping the LHS as `(<w> 0 <args> : <codomain>)`. The
bug is real (a point-free tail leaves the LHS a function whose implicit
type arguments are unconstrained). Test `tail_spin` in
`test_fuel_param.lem` + two pins in `TestFuelParamCheck.lean`
(`(tail_spin_lemFuel 0 n : Nat → Nat) = (fun x => x)`, `@tail_spin Nat ⟨3⟩
2 7 = 7 := by decide`) — built green in the suite.

**N10 — spot-check of three MEASURED rows against cerberus source @
`1b57bcf26`.** Row 15 `memValueFromValue` (`core_aux.lem:149-186`):
`let (Ctype annots ty_) = unatomic ty`, recursion `memValueFromValue
elem_ty …` with `elem_ty` from `Array elem_ty _` of `ty_`; `unatomic`
(`ctype.lem:240`) returns the `Atomic` payload or `ty` itself, so
`ctypeSize (unatomic ty) ≤ ctypeSize ty` and the measure `ctypeSize ty1`
strictly decreases — plausible; the body calls the fuel'd
`Ctype_aux.are_compatible`, consistent with "wrapper keeps `[LemFuel]`".
Row 61 `easy_update_mem_value_aux` (`defacto_memory.lem:2188-2250`):
every recursive call (array ×2, struct, union) passes `sh'`, the tail of
the matched `sh` — `List.length sh + 1` plausible. Row 24 `to_pure`
(`core_aux.lem:1530`): `to_pure_aux` recurses on `subst_pattern pat pe1
e2`, and `subst_pattern` (`:1479`) bottoms out in
`unsafe_subst_sym_expr`; the measure `exprSize g` is sufficient iff
substitution preserves the expr-node count — the lemma the record names
as the hard row; if `unsafe_subst_sym_expr` can add an expr node, the
obligation is unprovable and the row reclassifies (cerberus half's
proof is the test). Row 47 `step_eval_pexpr`: `self` is also passed as
a VALUE to `step_eval_peop` (`core_eval.lem:818`), so the measure's
sufficiency depends on that helper applying `self` only to `pe1`/`pe2`
components — the record already hedges this row.

**N11 — records' provenance and cites.** D1–D5 and the new decisions are
stated with [USER]/[AGENT] provenance and the operator's quotes
verbatim (both records §1, DESIGN "No magic values", rulings D4
addendum); the seam work list cites `1b57bcf26` = cerberus-lean primary
`HEAD` (verified `git rev-parse --short HEAD`); `.tmp/` retention is
stated in both records' "Not done" sections; the D4 `#eval`-level claim
is not in the record (added here, N6). Baseline-lem reproducibility
note: a `git archive 9ba8970` built INSIDE the worktree stamps itself
`Lem d8a17e3` (the version comes from the enclosing repo); identity
verified instead by grammar (it rejects `declare {lean} structural val`
with `Syntax error`; `strings … | grep -c fuel_measure` = 0 vs 28 for
this lem).

## Gates re-run in the audit worktree (fresh checkout of `d8a17e3`)

`make` (root): `exit=0`, `Lem d8a17e3`; ocamlyacc verbatim `5 rules
never reduced` / `2 shift/reduce conflicts, 2 reduce/reduce conflicts.`

`tests/comprehensive` `make lean` (`.tmp/suite-make-lean.log`), verbatim:
```
=== Generation: 51 passed, 0 failed, 0 skipped ===
Build completed successfully (151 jobs).
  OK (leg 1): panic prints the Incomplete Pattern message, then continues with default
  OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1
single-evaluation: OK
  OK: compiled draw sequences hold
  OK: compiled consumer injection holds
  OK (leg 1): two sufficient fuels agree; insufficient gives the declared sentinel; callee starts from the full ambient
  OK (leg 2): loud exhaustion at an insufficient runtime fuel fail-stops (exit 134)
  OK: inv_fuel.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_fuel_measure.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_reader_consumer.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_structural.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_supply.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: 236 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make lean  338.13s user 47.14s system 124% cpu 5:10.05 total
EXIT=0
```
Derived counts from the same log: 68 × `OK (rejected as declared)`;
parity 23 × `OK: parity`, 6 × `OK: both fail`, 4 × `XFAIL`
(`f_int_of_big_num`, `f_int32_overflow`, `p_str_bytes`, `p_str_escapes`);
non-XFAIL `FAIL` lines: only the four that precede those XFAILs.
Axiom lines, verbatim:
```
'TestStructuralCheck.len_append' depends on axioms: [propext, Quot.sound]
'TestStructuralCheck.rev_acc_length' depends on axioms: [propext, Quot.sound]
'TestFuelMonoExemplar.spin_stable' depends on axioms: [propext]
'TestFuelMonoExemplar.spin_fuel_irrelevant' depends on axioms: [propext]
'Test_fuel_measure_lemMeasureProofs.mlen_measure_sufficient' depends on axioms: [propext, Quot.sound]
'Test_fuel_measure_lemMeasureProofs.mspin_measure_sufficient' depends on axioms: [propext, Quot.sound]
'Test_fuel_measure_lemMeasureProofs.mev_measure_sufficient' depends on axioms: [propext, Quot.sound]
'Test_fuel_measure_tree_lemMeasureProofs.mtsum_measure_sufficient' depends on axioms: [propext, Quot.sound]
'Test_fuel_measure_tree_lemMeasureProofs.mdepth_measure_sufficient' depends on axioms: [propext, Quot.sound]
```

`tests/nonlean-regress/run.sh`, verbatim:
```
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
./tests/nonlean-regress/run.sh  102.40s user 5.85s system 99% cpu 1:48.28 total
```

`lean-lib` `lake build` (capped): `Build completed successfully (37 jobs).`;
`grep -rn "^axiom " . --include='*.lean' | wc -l` → `0`.

## Non-Lean blast radius: the cerberus OCaml tree

`frontend/` of cerberus-lean @ `1b57bcf26` copied to `.tmp/cerb-ocaml`;
the five numeric fuel lines (`driver.lem:1915-1918`,
`nondeterminism.lem:574`) deleted (`numeric lines left: … 0 … 0`);
`LEM_SRC` (86 files) from `make -s --eval`; the Makefile's flags
(`-wl ign -wl_rename warn -wl_pat_red err -wl_pat_exh warn -cerberus_pp
-ocaml`), `-lib` = this tree's `library`; baseline = `git archive 9ba8970`
rebuilt (`make build-lem`, 8 s). Verbatim:
```
base exit 0
new exit 0
files: base=86 new=86
OCAML DIFF exit 0 lines 0
```

## Plants (all restored; `git status` clean)

Obligation plants P1–P5 and P2b: quoted under M2/M5. No-numerals gate:
not re-planted (the record's §5.4 plant is quoted there; the F3 regex
was read: a numeral is matched only as the WHOLE counter argument).

## What was not checked

- The 38 cerberus obligation proofs and the dry-run's Lean build
  (`.tmp/cerb` in the arc worktree — ephemeral, not reproduced here);
  the D2 sibling rewrites' build; the `zip`-truncation finding for the
  cerberus equalities (cerberus-side).
- Monotonicity exemplar internals beyond the build/axiom lines (read:
  statements are the ones the record specifies; `spin_fuel_irrelevant`
  is stated at the wrapper with two completing fuels).
- Reader × measure and mutual × measure beyond the suite's own pins
  (`msum_amb`, `mev`/`modd` built and asserted in the suite).
- Human-target echo of the two new declares was not diffed against a
  golden beyond the net (the net's corpus has no source using them, as
  the record says).
- Ott derived artifacts (TODO row 5, pre-existing).
