# Fuel-parameter arc — pre-merge audit (2026-09-04)

Auditor [AGENT] (independent of the worker and the orchestrator). Range
audited: `arc/fuel-parameter` @ `82b14e4`, 7 commits above mainline
`mdd/lean-backend` @ `0890229` (`git diff 0890229..82b14e4`, 58 files).
Read-only inputs: the arc worktree, `deps/`, cerberus-lean (primary @
`de2fbf1bd`, worktree `zero-discrepancy` @ `a751e748e`). Everything below
was re-run in this audit worktree (`audit/fuel-parameter-premerge`, a
fresh `lem` built from `82b14e4` in 23 s; a BASELINE `lem` built from
`git archive 0890229` into `.tmp/base`). Every quoted output is verbatim
from those runs; tallies marked "derived" are derived. Gradings are
[AGENT]; the only [USER] text is the quoted rulings. Nothing merged,
nothing pushed; `.tmp/` is ephemeral.

## Verdict

**MERGE-WITH-FIXES.** No MAJOR finding: no magic value survives in
`src/`, `lean-lib/`, `library/` or the generated trees; the OCaml output
of the cerberus model and of the whole non-Lean regression corpus is
byte-identical; every fail-closed guard the record claims fires with the
quoted text; the `[LemFuel]` design meets the consumer's §3 requirements
1, 2 and 4 (requirement 3, monotonicity, is honestly declined — see N6).
The fixes are documentation-integrity items (M1, M2) and two gate-quality
items (M3, M4) that should land before the ff-merge; M5 may follow.

## Findings

### MINOR

**M1 — the manual asserts a library `fuel_consumer` that does not exist.**
`doc/manual/backend_lean.md` (Fuel section): "The library uses it once,
for `Relation.transitiveClosureByCmp`, whose `Pset.tc` iterates pset.ml's
unbounded `lfp` on the caller's fuel." Measured: `grep -rn fuel_consumer
library/` → no hits. That variant was BUILT AND WITHDRAWN (record §9 D1);
the sentence is a leftover of the withdrawn state, in the shop-window
manual. Fix: delete the sentence (or replace it with "the library
declares none").

**M2 — `DESIGN.md` "No magic values" contradicts itself.** The paragraph
says (draft, `0db35ec`): "A recursion bound COMPUTED inside a definition
(even from the data, e.g. a tree height) is hardcoded in that sense,
unless it is passed in by the calling context or eliminated by a
termination proof" — and, four sentences later (R1): "a recursion index
that is structurally recursive on a DATA measure (the AVL height stored
in a `Pset`/`Pmap` node) is admissible … the three admissible forms are a
caller parameter, a termination proof, and data-measure structural
recursion." The first sentence forbids exactly what the last admits.
This is the normative principle page; a reader (or the upstream
reviewer) cannot tell which rule holds. Fix: rewrite the paragraph as the
three admissible forms once, with the third-form ruling quoted; state
`Pset.tc`'s `(2|r|)²+1` explicitly as "data-derived bound, classified
(c), D1 pending" so the open decision is visible where the rule is.

**M3 — the no-numerals gate does not scan the parity modules on a clean
run.** Suite order (`tests/comprehensive/Makefile`): `… lean-fuel-param
lean-no-fuel-numerals lean-negative lean-invariance lean-parity`. The gate
lists `parity/lean-test/P_*.lean`, which `lean-parity` generates LATER.
Clean `make lean` in this worktree, verbatim:
`  OK: 173 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F4)`;
the same script run again after the parity phase: `OK: 219 files
scanned …`. The record's final-run "219" (§8.1) was therefore measured
on a tree where a previous run had left the `P_*` modules — the gate as
ordered never certifies them on a fresh tree (the 22 parity probes
include `p_fuel`, the one probe whose Lean driver instantiates the
fuel). Fix: move `lean-no-fuel-numerals` after `lean-parity` (or make the
parity runner call the gate on its own output).

**M4 — two fuel-literal shapes pass the gate green.** Plants in this
worktree (each appended to a scanned file, gate run, file restored):

```
EVASION E1 (parenthesised literal: spin_lemFuel (5) 3):
  OK: 219 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F4)
exit=0
EVASION E4 (wrapper applied at an explicit instance literal in generated code: @spin ⟨5⟩ 3):
  OK: 219 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F4)
exit=0
```

Neither shape is one the backend emits (F3 is aimed at `worker N`), but
LemLib and the generated library are hand-editable and `@f ⟨N⟩` is the
documented ENTRY-POINT idiom — the one most likely to be pasted into
library code by mistake. Fix: extend F3 to `_lemFuel[[:space:]]*\(?[[:space:]]*[1-9]`
and add F5 `⟨[[:space:]]*[1-9][0-9]*[[:space:]]*⟩` (an anonymous-constructor
literal; `⟨n⟩` with a variable stays legal). The four documented plants
all red correctly (§ Plants below), plus `instance : LemFuel where fuel
:= 5` (F2) and `LemFuel.mk plantK` via a named constant (F2), and
`attribute [instance]` on `def … := LemFuel.mk 5` (F4).

**M5 — `fuel_consumer` is not in the contextual-keyword acceptance
test.** The manual says the standing test covers "each word"; `grep -n
fuel_consumer tests/comprehensive/test_contextual_keywords.lem` → no
hits. Probe (this worktree): `let fuel_consumer = (1 : nat)`, a parameter
and a record field of that name compile on `-ocaml`, `-lean`, `-hol`
(exit 0 each; Lean renders `fuel_consumer`, `fuel_consumer2`,
`fuel_consumer0`) — the mechanism works; only the test is missing. Fix:
add the word to the test file's rows.

### NOTE

**N1 — a fuel-reading hand-written rep WITHOUT the `fuel_consumer`
declare is not refused at generation time.** The backend cannot see the
rep's body; the record does not claim otherwise, but the manual should
say what happens. Plant: `declare lean target_rep function consumer_spin
= \`TestFuelConsumerImpl.spinAtFuel\`` (an implementation taking
`[LemFuel]`) with no declare; `lem -lean` exit 0, callers NOT lifted
(`def uses_consumer (k : Nat) : Nat := TestFuelConsumerImpl.spinAtFuel k`);
Lean, verbatim:

```
Plant_norep_consumer.lean:29:45: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  LemFuel
```

Fail-closed at build time, and — because no instance exists anywhere —
it cannot be silently absorbed; that is the design's own safety net
working. Add one sentence to the manual's `fuel_consumer` paragraph.

**N2 — cerberus-half cites: correct at `de2fbf1bd`, stale at Z2.** Every
file:line in record §6.6 resolves at the primary checkout (`CerbMem.lean`
483/489/494/498/502/691/849/1016/1155/1183/1215 all `_lemFuel
lemDefaultFuel`; `CerbFuel.lean:71`; `CerbND.lean` 85/148/225/277/298–347/
389–412/450/467 within ±2 of the cites; `TotalityProofTest.lean:36-87`;
`EffectsProofTest.lean:55`; `FuelExemplar.lean` 204-205/222/238-239/253/
272/317; all `.lem` cites exact). At `zero-discrepancy` Z2 (`a751e748e`)
the `.lem` cites are unchanged and the Lean seams moved: `CerbMem.lean`
483→510, 489→516, 494→521, 498→525, 502→529, 691→747, 849-850→910-911,
1016→1085, 1155-1156→1227-1228, 1183→1255, 1215→1287; `CerbND.lean`
85→98, 150→162, 227→239, 280→291, 298-351→312-361, 389-413→403-426,
450→464, 467→481. The cerberus half should re-cite against its own base.
Also: "52 `rfl`s" at `TotalityProofTest.lean:36-87` — 52 is the line span;
47 lines carry `lemDefaultFuel … rfl` (derived).

**N3 — derived counts in record §6.4 are internally inconsistent.**
"fuel-declared vals 64 (69 declares minus the 5 numeric)" against
"wrappers … 67 in 15 files". Recount over `LEM_SRC_LEAN` at `de2fbf1bd`
(derived, `grep -c '^declare {lean} fuel val'`): **72 declares in 15
files**, 72 − 5 = **67** sentinel declares = the 67 wrappers = the 67
`_zero` lemmas. The 69/64 figures look mis-derived; the 67s are
consistent. Also `LEM_SRC`/`LEM_SRC_LEAN` via `make --eval` at
`de2fbf1bd`: 86/85 files (record: 87/86; the record's "cerberus-lean
HEAD" is not pinned to a hash). Not re-counted (needs a successful Lean
generation of the dry-run tree, which the D2 sites block by design):
370 `[LemFuel]` defs, 26/41 worker split, 0 literals.

**N4 — cross-reference slip.** The X3 addendum
(`2026-09-03_exception-case-rulings.md:95-`) says "listed in
`2026-09-04_fuel-parameter-record.md` §7" for the LemLib behaviours
examined; §7 is Perf — the list is §4 (table) and §9 D4.

**N5 — `heightsOk` is assumed, not proven preserved.** `join_eq` holds
under `heightsOk l ∧ heightsOk r`; nothing in LemLib proves `add`/`bal`/
`create`/`join` preserve it. On a tree violating it (constructible only by
hand via the public `Node` constructor; every port operation mirrors the
OCaml's invariant-preserving code) the indexed `joinGo` exhausts LOUDLY
where the OCaml — and the pre-arc WF `join` — compute. Unreachable
through the API; the consumer's Pmap-laws slice is the named prover of
preservation. No action for this merge; record it as the temporal
boundary it is.

**N6 — monotonicity (record §5): the negative claim is correct for the two
shapes it considers, but "requires an absorbing typed outcome" overstates
it.** (i) With the opaque payload, "≠ payload" is indeed unstatable; (ii)
with a value payload, "result ≠ payload at n ⇒ same at n+1" is indeed
false (a body may branch on a sub-call's sentinel), and worse, a genuine
result may EQUAL the sentinel value, so "≠ sentinel" is not even a sound
completion predicate. What the record does not consider: the backend can
GENERATE a completion predicate `f_completes : Nat → args → Bool` that
mirrors the worker (0 ↦ false; n+1 ↦ the body with every recursive call
replaced by "call at n AND completes at n"), and then
`f_completes n x = true → f_lemFuel (n+1) x = f_lemFuel n x` and
`f_completes n x → f_completes (n+1) x` are provable by induction on n
for ANY body, since a body is a function of its sub-results — no monad,
no absorbing element needed. Cost: a second, instrumented copy of every
worker (the body transformation is essentially a Bool-writer
instrumentation of the recursive calls), and the statement is per
function, not one generic lemma. Whether that is preferable to the
absorbing-monad route (which cerberus's `NDkilled`/`nd_bind` already
provides for the driver family) is an operator decision; TODO row 13
should list both routes rather than name one as required.

**N7 — `deps/lem-pinned`'s binary is stale.** `deps/lem-pinned/lem -v` →
`Lem dff1957` while the checkout is at `3c88f0d`; it fails on cerberus
`utils.lem:90` (`declare {lean} ground_rep …`, "Syntax error"). The
byte-identity comparison below therefore used the opam-installed `lem`
(`_opam/bin/lem`, `Lem 3c88f0d`, what cerberus actually builds with) and
the archive-built `0890229`. Container hygiene, not this arc's; flagged
for the operator (CLAUDE.md's "in-tree `./lem` goes stale" gotcha applies
to `deps/lem-pinned` too).

**N8 — D1 (`Pset.tc`) assessment.** Read `tc`: `n := cardinal r`;
`lfpGo cmp oneStep ((2*n)*(2*n) + 1) r`. Every productive `lfp` step adds
≥1 pair from the ≤(2n)² pairs over r's endpoints, so the closure is
reached within (2n)² − n productive steps plus the terminating check:
the bound is a theorem about the data, not a choice, and it is exact in
the sense that matters (no run that terminates in OCaml can exhaust it,
for any comparator that is a total preorder). Classification (c) is
defensible; the only difference from the height indices is that the
height is STORED while this is COMPUTED — not a principled line, and
DESIGN.md currently draws it both ways (M2). `lfpGo` is "(a)" only
nominally: its sole caller is `tc`; no lem-level entry passes a fuel to
it. Leave the operator decision open as the record does; fix the
principle text.

**N9 — `lemLeastFixedPoint` D3.** Confirmed untouched in the diff (no hunk
touches it); `| 0 => x` mirrors `set.lem` `leastFixedPoint` — lem's own
design choice. Agree with the disposition and its provenance ([AGENT]
applying the quoted [USER] general form).

## Scope 1 — no magic values: evidence

- Tree greps (arc tree): `lemDefaultFuel` in `src/ lean-lib/ library/` →
  only the HISTORY comment in `LemLib.lean:63` and the History comment in
  `lean_backend.ml:1552`; `fuel_budget|Decl_fuel_budget` → no hits;
  `lemOcamlInt*` → no hits; `native_decide|bv_decide|ofReduce|maxHeartbeats|
  maxRecDepth|^axiom` in `lean-lib/*.lean` → only the header sentence
  naming them as banned.
- Every `| 0 =>`/`| 0,` arm in LemLib: `gen_pow_aux` (`| 0 => one`, the
  mathematical base case), `joinGo`/`unionGo`/`interGo`/`diffGo`/
  `compareAux`/`subsetGo`/`lfpGo`/`Pmap.joinGo`/`mergeGo`/`equalAux`/
  `compareAux` — all `fuelExhaustedWith` (loud), `lemLeastFixedPoint`
  `| 0 => x` (lem's own, D3). No silent arm other than the ruled one.
- The numeric form is refused at the PARSER (`src/parser.mly`, the
  production kept only to raise), so no downstream path can receive a
  budget: `const_descr.fuel_budget` is gone (`typed_ast.mli`), no
  `fuel_budget_for` in the emitter; the wrapper renders the literal text
  `" LemFuel.fuel"` (`lean_backend.ml`, wrapper assembly). Verbatim
  refusal (this worktree's `lem` on `negative/neg_fuel_numeric_budget.lem`):

```
  Syntax error: the numeric fuel-budget form 'declare {lean} fuel val f = N' was removed (fuel-parameter arc, 2026-09-04): a per-declaration fuel literal is a magic value -- [USER 2026-09-03] (ruling against hard-coded magic values; message text paraphrased here)
```

  and on the ORIGINAL cerberus sources (first of the five):
  `File "frontend/model/nondeterminism.lem", line 574, character 1 to line 574, character 43` + the same text.
- `lfpGo`'s only caller is `tc` (N8); no call site passes a numeral.

### The gate, plant-tested (this worktree, `check_no_fuel_numerals.sh`)

```
PLANT A (F3: generated worker at a literal fuel):
  FAIL (F3): fuel numeral shape found:
…/tests/comprehensive/Test_fuel_param.lean:131: def plantA : Nat := spin_lemFuel 5 3
exit=1
PLANT B (F2+F4: global instance in LemLib):
  FAIL (F2): fuel numeral shape found:
…/lean-lib/LemLib.lean:1842: instance : LemFuel := ⟨1000000⟩
  FAIL (F4): fuel numeral shape found:
…/lean-lib/LemLib.lean:1842: instance : LemFuel := ⟨1000000⟩
exit=1
PLANT C (F1: code reference to lemDefaultFuel):
  FAIL (F1): fuel numeral shape found:
…/lean-lib/LemLib.lean:1842: def plantC : Nat := lemDefaultFuel
exit=1
PLANT D (F2 variant: instance … where fuel := 5):
  FAIL (F2): fuel numeral shape found:
…/lean-lib/LemLib.lean:1842: instance : LemFuel where
exit=1
EVASION E2 (named constant instance: def k := 5; instance : LemFuel := LemFuel.mk k):
  FAIL (F2): fuel numeral shape found:
…/lean-lib/LemLib.lean:1843: instance : LemFuel := LemFuel.mk plantK
exit=1
EVASION E3 (attribute [instance] on a def):
  FAIL (F4): fuel numeral shape found:
…/lean-lib/LemLib.lean:1842: def plantInst : LemFuel := LemFuel.mk 5
exit=1
REVERTED:
  OK: 219 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F4)
exit=0
```

(E1/E4, the two green evasions, are M4.) The vacuity guards (≥40 files,
≥1 `_lemFuel`) are present in the script.

## Scope 2 — the `[LemFuel]` design vs the consumer's §3

- **Single fuel position.** The wrapper is emitted as literal text
  `def f [LemFuel] … := f_lemFuel LemFuel.fuel`; workers pass only their
  own decremented counter to self/sibling calls (`fuel_workers`); a worker
  that reaches fuel OUTSIDE its block takes `[LemFuel]` and its callees'
  wrappers restart from `LemFuel.fuel` (`workers_need_fuel`). Generated
  evidence: `def outer_lemFuel [LemFuel] (lemFuel : Nat) …`,
  `mping_lemFuel`/`mpong_lemFuel` likewise; leaf workers carry no
  instance. Hand-written reps read `LemFuel.fuel`
  (`TestFuelConsumerImpl.spinAtFuel [LemFuel]`). No other source found.
- **Call sites textually unchanged.** Regenerated `test_target_reps.lem`
  with the baseline (`0890229`) and this lem into separate dirs; `diff`:
  36 changed lines, every one either a wrapper (`lemDefaultFuel` →
  `[LemFuel] … LemFuel.fuel`), an added `theorem …_lemFuel_zero … := rfl`,
  or a `[LemFuel]` binder inserted after the def name; the right-hand
  sides are byte-identical (e.g. `uses_countdown [LemFuel]   (k  : Nat)   :
  Nat :=  fuel_countdown  k  +   1`, HOF `List.map ( fuel_env_loop
  _lemReader_ambient_env)  l` unchanged). Fuel-free modules
  (`test_collections`, `test_classes`): 0 changed lines. This also
  verifies record §3 exactly.
- **All-or-none propagation.** `lean_fuel_prepass` is a fixpoint at
  `Val_def` granularity over `used_consts` (fuel'd ∪ consumer ∪ lifted);
  instances are skipped and refused at emission (`exp_needs_fuel … inside_instance`);
  `Let_def` values lifted (`let_fuel_lifted`; generated `def spun_value
  [LemFuel] : Nat`). Cross-invocation probe (module A with the fuel'd def
  supplied via `-i`, only B emitted): B's callers of A's NON-fuel'd
  lifted def still get `[LemFuel]` (`def only_lifted [LemFuel] …`) — the
  prepass sees included modules, as the reader lifting does. I found no
  def that reaches a fuel'd def and lacks the binder.
- **`fuel_consumer`.** FC-rep and FC-inert fire, verbatim:
  `Error: Lean backend: val f is declared {lean} fuel_consumer but has no Lean target_rep (FC-rep: …)`;
  `Error: Lean backend: 'declare {lean} fuel val spin' on a val that carries a Lean target_rep (FC-inert: …)`.
  The undeclared-rep case is N1 (build-time, not generation-time).
- **`_zero` lemmas.** Generated `Test_fuel_param.lean`, verbatim: `theorem
  spin_lemFuel_zero ( n : Nat) :\n    spin_lemFuel 0  n = (999) := rfl`;
  `theorem climb_lemFuel_zero (_lemReader_amb : Nat) ( n : Nat) :\n
  climb_lemFuel 0 _lemReader_amb  n = (998) := rfl` (reader-lifted);
  `theorem outer_lemFuel_zero [LemFuel] ( n : Nat) :\n    outer_lemFuel 0
  n = (fuelExhausted n) := rfl` (ambient-passing worker: instance carried);
  `Test_supply.lean`: `fuel_draws_lemFuel 0 _lemSupply_tick  n = (([]),
  _lemSupply_tick) := rfl` (supply pairing). Sentinel text comes from the
  one shared renderer `fuel_sentinel_output` (read). Suite tree (derived):
  16 wrappers, 16 `_zero` lemmas, 0 "not generated" comments.
- **§4.3 no-ambient-fuel contexts.** Verbatim (this lem): assert —
  `neg_fuel_scope_assert.lem, line 11, character 19 to line 11, character 24 / Error: Lean backend: fuel'd (or fuel-lifted) definition referenced outside a fuel scope — an application — where no [LemFuel] instance is in scope (instance methods, indreln rules, lemmas/asserts cannot take the ambient fuel; fuel is a parameter of the semantics with no default: call the definition from a fuel-lifted definition, or from hand-written Lean that supplies the fuel, e.g. \`@f ⟨n⟩ …\` or \`letI : LemFuel := ⟨n⟩\`) / original input: "spin 3"`;
  instance — `Error: Lean backend: fuel'd (or fuel-lifted) call inside an instance method (unsupported: instance fields cannot take the [LemFuel] binder) / original input: "spin x"`;
  indreln (my plant `r1: forall n. spin n = 0 ==> ok n`) — the same
  "outside a fuel scope" error at `line 6, character 15 to line 6, character 20`, `original input: "spin n"`;
  cerberus dry run (edited scratch, `-lean`) stops at the first D2 site,
  verbatim: `File "frontend/model/ctype.lem", line 183, character 14 to line 183, character 23 / Error: Lean backend: fuel'd (or fuel-lifted) call inside an instance method (unsupported: instance fields cannot take the [LemFuel] binder) / original input: "ctypeEqual"` (16 modules emitted before it).
- **Entry point.** `p_fuel` re-run (this worktree, clean): `=== p_fuel ===
  / OK: parity (16 lines byte-identical to the OCaml reference; pin
  matches)` — the Lean driver evaluates `@results ⟨200⟩` and `@results
  ⟨100000⟩`, the OCaml driver prints its fuel-free block twice; the
  compiled pin: `OK (leg 1): two sufficient fuels agree; insufficient
  gives the declared sentinel; callee starts from the full ambient` /
  `OK (leg 2): loud exhaustion at an insufficient runtime fuel fail-stops
  (exit 134)`. `TestFuelParamCheck` (9) pins the `letI` shape by `decide`.
- **Monotonicity:** N6.

## Scope 3 — LemLib rewrites

- `Pset.joinGo`/`Pmap.joinGo` read against pset.ml:86 / pmap.ml:185: the
  three arms (`Empty,_`; `_,Empty`; the `lh > rh + 2` / `rh > lh + 2` /
  `create` split) are the OCaml's, with the index threaded; `join` applies
  `height l + height r + 1`. `heightsOk` is `h == max hl hr + 1` at every
  node (Bool, decidable). `joinGo_eq` descends into the taller side's
  child whose stored height is strictly smaller under `heightsOk`, so the
  index exceeds the depth; `join_eq` follows with `omega`. Proof methods:
  `induction`, `cases`, `simp only`, `split`, `rw`, `omega`, `rfl` — no
  banned method, no option bump. `lake build` of `lean-lib` (capped,
  this worktree): `Build completed successfully (37 jobs).`, verbatim
  axioms: `'LemLibTheorems.PsetJoin.join_eq' depends on axioms: [propext,
  Classical.choice, Quot.sound]`, `'LemLibTheorems.PmapJoin.join_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]`; the twelve
  F7 theorems unchanged (`[propext]` … `[propext, Quot.sound]`).
- `LemLibTest.lean` closed-term `decide`s reach `join`: `Pset.union` →
  `unionGo` → `join`; `Pset.remove` → `merge`/`bal`; `Pmap.union`/`remove`;
  `fmapUnionBy` = `Pmap.union`, `fmapDeleteBy` = `Pmap.remove` (read); all
  build (part of the 37 jobs).
- `lemNatFromNatural`/`lemIntFromInteger` are `n`/`i`; `lemOcamlIntMax/Min`
  deleted with no other user (grep). No other conversion touched in the
  `lean-lib/` diff (read in full); `natFromNumeral`/`intFromNumeral` stay
  literal pass-throughs. Parity runner, verbatim: `=== f_int_of_big_num ===
  / ocaml: failed as expected (exit 2): Fatal error: exception
  Failure("int_of_big_int") / FAIL: failure probe, but the Lean binary
  SUCCEEDED (exit 0) where the OCaml reference fails / XFAIL (expected,
  registered): RULED OCaml-target deviation ([USER 2026-09-03] ruled that
  hard-coded OCaml-level limits are forbidden too, the logical semantics
  being what counts): …` (runner text paraphrased here).
- `lemLeastFixedPoint`: untouched (N9).

## Scope 4 — non-Lean blast radius

- `tests/nonlean-regress/run.sh` (this worktree, this lem), verbatim:

```
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
tests/nonlean-regress/run.sh  121.70s user 6.54s system 99% cpu 2:08.55 total
EXIT 0
```

- Cerberus OCaml tree. Method: `LEM_SRC` expanded read-only with `make
  --eval` at `de2fbf1bd` (86 files); the `.lem` files copied under
  `.tmp/cerb/{orig,edit}`; `edit` = the five numeric declare lines deleted
  (`sed`; 0 remain); flags `-wl ign -wl_rename warn -wl_pat_red err
  -wl_pat_exh warn -cerberus_pp -ocaml`. Lems: `_opam/bin/lem` (`Lem
  3c88f0d`), archive-built `0890229`, this tree's (`82b14e4`). Results:
  `opam-edit exit=0 files=86`, `opam-orig exit=0 files=86`, `base-orig
  exit=0 files=86`, `base-edit exit=0 files=86`, `new-edit exit=0 files=86`,
  `new-orig exit=1 files=0` (the refusal quoted in Scope 1). Byte
  comparisons, verbatim:

```
== DIFF opam(3c88f0d)-edit vs new-edit:
exit=0 lines=0
== DIFF base-edit vs new-edit:
exit=0 lines=0
== DIFF opam-orig vs base-orig:
exit=0
== DIFF opam(3c88f0d)-orig vs new-edit:
diff -r …/out-opam-orig/driver.ml …/out-new-edit/driver.ml
2308a2309,2313
> (* FUEL arc budget commit (design note section 4): the coupled driver
>    quartet runs at CerbFuel.driverFuel = 10^8 (L1 numeric form: WRAPPER
>    budget only; opt-in). CerbND.lean pins each wrapper to the named
>    constant (driver2_wrapper_defeq and siblings) and driverFuel_eq gives
>    the numeral. *)
exit=1 lines=7
```

  The record's claim (§6.2: empty on the same sources; exactly one
  5-line comment hunk at `driver.ml:2308a2309,2313` against the original
  sources, the comment the deleted `declare` line had swallowed) is
  verified exactly. That hunk is a property of the SOURCE EDIT under any
  lem (a `{lean}` declare emits `emp` including its leading skips), not
  of this backend change.
- Invariance phase (clean run), verbatim: `OK: inv_fuel.lem (7 artifacts
  byte-identical across ocaml/hol/isa/coq)` / `OK: inv_reader_consumer.lem
  (5 artifacts …)` / `OK: inv_supply.lem (5 artifacts …)`.
- `src/backend.ml`: the only non-Lean-emitter hunk is the human-target
  echo of the declare (`fuel_consumer` replaces the budget echo); every
  non-human target returns `emp` as before. `lexer.mll` adds the
  contextual keyword (M5 probe shows identifiers unaffected).

## Scope 5 — record integrity

Re-run verbatim lines that match the record: `=== Generation: 47 passed,
0 failed, 0 skipped ===`; `Build completed successfully (136 jobs).`; the
two `lean-fuel-param` OK lines; the three invariance OK lines; `=== p_fuel
=== / OK: parity (16 lines byte-identical …)`; the `f_int_of_big_num`
XFAIL block; `nonlean-regress: OK (893 artifact rows, 216 exit rows, 9
emitters, byte-identical to golden)`; the two `join_eq` axiom lines;
`Build completed successfully (37 jobs).`; `'TestFuelParamCheck.spin_fuel_irrelevant'
depends on axioms: [propext, Quot.sound]` Derived counts this run:
negative `OK (rejected as declared)` × 45 (record: 45); parity OK 21 /
both-fail 7 / XFAIL 3 (record: 21 / 7 / 3 incl. the two F2 rows). Wall:
`make lean  312.72s user 43.96s system 121% cpu 4:52.85 total` (record
6:29.70 — the record's run included the pin-recording work). Divergences
from the record: the gate's file count (M3), the §6.4 counts (N3), the
cites (N2), the §7 cross-ref (N4). Provenance: D1–D5 are marked [AGENT]
or "operator decision"; every [USER] tag I checked sits on a quoted
ruling; D3's "RESOLVED BY RULE [AGENT applying the USER rule]" is the
correct form.

## Not checked

- The cerberus Lean generation counts (370 / 26 / 41 / 0) — the dry-run
  tree needs the four D2 patches to generate; not patched here (N3).
- Lean compilation of the cerberus generated tree, any differential lane,
  the `.lake`/perf shape-1 numbers (report-only in the record), the Ott
  artefacts (TODO row 5), Isabelle/HOL/Coq semantic content beyond
  byte-identity, and the consumer's downstream restatement (§6.7) —
  outside this repo.
- Whether `heightsOk` is preserved by every LemLib operation (N5; the
  consumer's slice).

## Runs and budget

Nothing exceeded 10 min: lem build 23 s; baseline build ≈25 s; `make
lean` 4:53; nonlean-regress 2:09; cerberus OCaml regeneration ×6 ≈40 s
each; lean-lib build < 2 min. Total ≈ 1 h 05.
