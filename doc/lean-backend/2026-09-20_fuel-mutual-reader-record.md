# Fuel × reader × truly-mutual blocks — record (2026-09-20)

Branch `mutual-fuel-readers` (lem-lean), from mainline `mdd/lean-backend`
@ `4307dc5` (= the cerberus-lean pin after S0.5). Charter: cerberus-lean
`lean_frontend/docs/2026-09-20_charter-program-data-parameters-S1.5.md`,
Part A; the motivating failure is E-A Phase 1's first regeneration with
the enum reader declared (verbatim there, `lean_frontend/lem.log:384-386`):

```
File "frontend/model/ail/ailTypesAux.lem", line 784, character 1 to line 862, character 51 processed by: compile_faux_seplist, mk_case_exp
  Error: Lean backend: 'declare {lean} fuel val' in a mutual block combined with reader lifting (unsupported; extend when needed)
```

Worker [AGENT] (Fable-class, chartered — the S0.5 lem-lean worker
resumed); rulings quoted with provenance; every quoted output is verbatim
from this worktree (`worktrees/lem-lean-mutual-fuel-readers`, logs under
its ephemeral `.tmp/`: `suite_a2.log`, `sweep.log` + `sweep/`, `gen_new/`,
`probe_old/`); tallies marked "derived" are derived. Nothing merged,
nothing pushed; `lean-lib/` untouched (`git diff --stat 4307dc5 --
lean-lib` → empty); `deps/lem-pinned` and the switch's `lem` untouched
(the orchestrator's boundary step).

## 0. Commit

| Commit | Content |
|---|---|
| this commit | `src/lean_backend.ml`: the guard at `:4604-4606` deleted, two comments reworded (nothing else); `tests/comprehensive/test_fuel_mutual_reader.lem` + `lean-test/TestFuelMutualReader{Check,Exec}.lean` + `lean-test/Test_fuel_mutual_reader_lemMeasureProofs.lean` + lakefile roots/exe + Makefile phase `lean-fuel-mutual-reader`; `negative/neg_fuel_mutual_lifted.lem` DELETED, `negative/neg_fuel_mutual_supply.lem` added; `invariance/inv_fuel_mutual_reader.lem`; `DESIGN.md` (fuel paragraph + `fuel val` row); this record |

## 1. Rulings honoured

- [USER 2026-09-19] delegation (charter §0): implementation-focused —
  the semantics does not move; a backend limit is lifted so the decided
  E-A route generates.
- [USER 2026-09-04]: the lem structure is not changed for OCaml's sake — the
  `are_compatible` blocks need the enum map on BOTH targets, so the
  backend composes the mechanisms; no `.lem` reshaping. The invariance
  witness (§3.4) shows the `{lean}` declares are no-ops for the other
  emitters.
- [USER 2026-09-08] nothing new is to be built out of policy — a guard
  deletion, tests/probes, docs, this record; the
  kernel pins are `rfl`/`decide` on concrete values and one joint
  stability proof in the C2 template.

## 2. The original gap (`a618b9c`) and why it no longer holds

`a618b9c` "Lean backend: fuel composes with mutual blocks (arc 3, B2)"
(2026-08-18) introduced the block-level fuel plan (`St.fuel_workers`:
sibling calls rewrite to `(worker lemFuel)`, all-or-none per block,
wrappers after `end`) and, in the same change, NARROWED the earlier
refusal "`'declare {lean} fuel val' in a mutual block (unsupported)`" to
"`… in a mutual block combined with reader lifting (unsupported; extend
when needed)`". Its message states the reason in one clause — *"fuel'd-
mutual x reader-lifting stays fail-closed"* — and the emission comment of
the time read *"Fuel emission: single-clause, non-mutual, non-instance,
not reader-lifted (extend on need — fail closed on every unsupported
combination)"*: **a scope cut, not a technical obstacle** — B2 built
fuel × mutual and B1 (the same arc) built fuel × reader for single defs,
and their composition was left fail-closed for want of a consumer.

Why it holds trivially now (verified on the code at `4307dc5`, then
empirically §3): every piece of the fuel'd emission is already generic
in the per-member `lifted` flag — the worker sets `St.reader_binder :=
lifted` (`:4652`), the point-free wrapper's `reader_arrows` (`:4741-4747`),
the measured wrapper's and the obligation's `reader_binders`/`reader_args`
(`:4836-4866`), the `_zero` lemma's `reader_binder_output ()` and
`(if lifted then reader_args_output () …)` (`:4905-4918`), and the
sibling-call rewrite `(sibling_lemFuel lemFuel <readers>)` at the
`St.fuel_workers` lookup (`:5961-5968`, `readers = if !St.reader_binder
…`). All-or-none lifting of a mutual block is STRUCTURAL: the reader
prepass records one `(defined, used)` pair per `Val_def` (`:1193-1201`),
so a mutual block's members are lifted together (`:1215` `union defined`).
Nothing else was needed — no fixpoint change, no LemLib change, no
grammar change (stop rule S1 not triggered).

## 3. What changed and what it emits

### 3.1 The backend (`src/lean_backend.ml`; `git diff --stat`: `22 +-`)

- Deleted (verbatim, at `4307dc5:4604-4606`):
  ```
                       | Some _ when is_truly_mutual && lifted ->
                         raise (Reporting_basic.err_general true (locn_of_clause_group g)
                           "Lean backend: 'declare {lean} fuel val' in a mutual block combined with reader lifting (unsupported; extend when needed)")
  ```
- Reworded: the fuel-emission comment (`:4442-4444` → the composition and
  the remaining refusals) and the "fuel x reader composes (arc 3, B1)"
  comment (now states the per-member mutual case and the sibling-call
  re-injection).
- KEPT, unchanged: `reader_seed` in a mutual block (`:4503-4505`),
  supply lifting in a truly-mutual block (`:4570-4572` — the remaining
  composition gap, now probed for the fuel'd shape §3.3), fuel/`fuel_measure`
  all-or-none, the instance refusals. Build: `scripts/ce make` → `./lem`,
  `Lem 4307dc5-dirty`; zero warnings attributed to `lean_backend.ml`.

### 3.2 The emitted shapes (verbatim, `./lem` on `test_fuel_mutual_reader.lem`)

Both members read the reader — workers `(lemFuel) (reader) (own)`, sibling
calls pass the decremented counter AND the reader, wrappers after `end`
point-free and reader-prefixed, `_zero` lemmas with the reader binder:

```
mutual
 def  rping_lemFuel (lemFuel : Nat) (_lemReader_amb : Nat)  (n : Nat)  : Nat := match lemFuel with
  | 0 => (991)
  | Nat.succ lemFuel => ( if  n  == _lemReader_amb then   0  else (rpong_lemFuel lemFuel _lemReader_amb)  (n  +   1))
def  rpong_lemFuel (lemFuel : Nat) (_lemReader_amb : Nat)  (n : Nat)  : Nat := match lemFuel with
  | 0 => (992)
  | Nat.succ lemFuel => ( if  n  == _lemReader_amb then   1  else (rping_lemFuel lemFuel _lemReader_amb)  (n  +   1))
end

def rping [LemFuel] : (Nat) -> Nat → Nat := rping_lemFuel LemFuel.fuel
theorem rping_lemFuel_zero (_lemReader_amb : Nat) ( n : Nat) :
    rping_lemFuel 0 _lemReader_amb  n = (991) := rfl
```

A block reaching a fuel'd callee (`cdown`) — the workers take `[LemFuel]`
(`workers_need_fuel`) with the reader, and so does the `_zero` lemma:

```
mutual
 def  fping_lemFuel [LemFuel] (lemFuel : Nat) (_lemReader_amb : Nat)  (n : Nat)  : Nat := match lemFuel with
  | 0 => (961)
  | Nat.succ lemFuel => ( if  n  ==   0 then  cdown  (_lemReader_amb)  else (fpong_lemFuel lemFuel _lemReader_amb)  (n  -   1))
def  fpong_lemFuel [LemFuel] (lemFuel : Nat) (_lemReader_amb : Nat)  (n : Nat)  : Nat := match lemFuel with
  | 0 => (962)
  | Nat.succ lemFuel => ( if  n  ==   0 then   1  else (fping_lemFuel lemFuel _lemReader_amb)  (n  -   1))
end

def fping [LemFuel] : (Nat) -> Nat → Nat := fping_lemFuel LemFuel.fuel
theorem fping_lemFuel_zero [LemFuel] (_lemReader_amb : Nat) ( n : Nat) :
    fping_lemFuel 0 _lemReader_amb  n = (961) := rfl
```

The measured pair — fuel-free wrappers binding the reader then the
parameter, and the obligations with the reader binder in the generic
position (as `msum_amb`'s single-def obligation has it):

```
mutual
 def  rmev_lemFuel (lemFuel : Nat) (_lemReader_amb : Nat)  (l : List (Nat))  : Bool := match lemFuel with
  | 0 => (false)
  | Nat.succ lemFuel => ( match  l with  |  [] => _lemReader_amb  ==   0 |  _  ::  xs => (rmodd_lemFuel lemFuel _lemReader_amb)  xs )
def  rmodd_lemFuel (lemFuel : Nat) (_lemReader_amb : Nat)  (l : List (Nat))  : Bool := match lemFuel with
  | 0 => (true)
  | Nat.succ lemFuel => ( match  l with  |  [] =>  not  (_lemReader_amb  ==   0) |  _  ::  xs => (rmev_lemFuel lemFuel _lemReader_amb)  xs )
end

def rmev (_lemReader_amb : Nat) ( l : List (Nat)) : Bool := rmev_lemFuel (List.length l + 1) _lemReader_amb  l
theorem rmev_lemFuel_zero (_lemReader_amb : Nat) ( l : List (Nat)) :
    rmev_lemFuel 0 _lemReader_amb  l = (false) := rfl
```
```
theorem rmev_measure_sufficient (_lemReader_amb : Nat) ( l : List (Nat)) (lemFuel : Nat) (lemMeasureLe : (List.length l + 1) ≤ lemFuel) :
    rmev_lemFuel lemFuel _lemReader_amb  l = rmev _lemReader_amb  l :=
  Test_fuel_mutual_reader_lemMeasureProofs.rmev_measure_sufficient _lemReader_amb  l lemFuel lemMeasureLe
```

(`rmodd`'s wrapper/obligation are the same with `(true)`; the one-reader
pair `oping`/`opong` renders like `rping`/`rpong` — `opong`'s body never
mentions the reader, its binder is there all the same.) The lifted caller:
`def  uses_rping [LemFuel] (_lemReader_amb : Nat)  (k : Nat)  : Nat := ( rping _lemReader_amb)  k`.

### 3.3 Tests

- `test_fuel_mutual_reader.lem`: reader `amb`; (1) `rping`/`rpong` both
  reading it (the reader decides which member reaches it: 0 vs 1; the
  sentinel of the member whose counter hits 0), a lifted caller
  `uses_rping`; (2) `oping`/`opong` where only `oping` reads it (all-or-none
  lifting); (3) `cdown` fuel'd + `fping`/`fpong` calling it from a member
  (`workers_need_fuel` with readers; the callee starts from the FULL
  ambient: `fping 2` at ambient 8 = 0, at 7 = 971 — the remaining counter
  after 3 hops, 5, would exhaust); (4) the measured `rmev`/`rmodd`
  (`List.length l + 1`) reading the reader in the base case. Nothing is
  assertable from the `.lem` (all lifted / ambient-fuel'd) — the pins are
  in Lean, as for the reader tests.
- `TestFuelMutualReaderCheck.lean`: signature pins (workers `Nat → Nat →
  Nat → Nat`, `[LemFuel]` on `fping_lemFuel`/`fpong_lemFuel`, wrappers
  `[LemFuel] : Nat → Nat → Nat`, measured wrappers fuel-free), binder
  NAMES/order via named arguments (`rping_lemFuel (lemFuel := 100)
  (_lemReader_amb := 7) (n := 3) = 0`), fuel-parametricity (`@rping ⟨n⟩ =
  rping_lemFuel n := rfl`, `@fping ⟨n⟩ = @fping_lemFuel ⟨n⟩ n`), the six
  `_zero` lemmas applied, the value pins of §3.3(1)–(4) by `decide`,
  `rmev_lemFuel 1 5 [1, 2] = true` (below the measure: the sibling's
  sentinel) vs the obligation applied at the measure; `#print axioms`.
- `TestFuelMutualReaderExec.lean` (`lean_exe test-fuel-mutual-reader`,
  phase `lean-fuel-mutual-reader`): eleven compiled re-assertions →
  `fuel mutual reader: OK`.
- `Test_fuel_mutual_reader_lemMeasureProofs.lean`: `rmev_rmodd_stable`
  (one joint induction on the list generalizing the two fuels, the reader
  an inert parameter — the `mev`/`modd` template verbatim plus the
  binder) and the two `_measure_sufficient` theorems it instantiates.
- `negative/neg_fuel_mutual_lifted.lem` DELETED (its EXPECT text no longer
  exists); before deletion its shape was run under both lems — the new
  lem ACCEPTS it (`exit 0`), the pinned lem refuses it (verbatim):
  ```
  File "negative/neg_fuel_mutual_lifted.lem", line 11, character 23 to line 11, character 69
    Error: Lean backend: 'declare {lean} fuel val' in a mutual block combined with reader lifting (unsupported; extend when needed)
    original input: "if n = neg_env () then 0 else neg_rpong (n - 1)"
  ```
  The positive family above is its successor.
- `negative/neg_fuel_mutual_supply.lem` ADDED (`EXPECT: supply lifting in
  a (truly) mutual block`): a FUEL'D truly-mutual block drawing a supply —
  the shape a user of the new composition tries next. `neg_supply_mutual.lem`
  already pinned the un-fuel'd block, with the weaker fragment `mutual
  block`; the new probe pins the fuel'd shape with the exact text (the
  supply refusal at `:4570-4572` precedes the fuel emission). Verbatim:
  ```
  File "negative/neg_fuel_mutual_supply.lem", line 17, character 19 to line 17, character 58
    Error: Lean backend: supply lifting in a (truly) mutual block (unsupported; extend when needed — acyclic rec-and blocks de-mutualize and thread fine)
    original input: "if n = 0 then tick () else spong (n - 1)"
  ```

### 3.4 Invariance witness

`invariance/inv_fuel_mutual_reader.lem`: the test's shape with a lem body
for the rep'd reader; the `{lean}` declares stripped leave ocaml/hol/isa/coq
byte-identical (§5).

## 4. The A3 byte-identity sweep (pinned `Lem 4307dc5` vs new `./lem`)

`.tmp/sweep.sh` (ephemeral): for each corpus, generate twice into
`-outdir` scratch trees (`.tmp/sweep/{pin,new}/`, per-invocation logs
kept OUTSIDE the trees under `.tmp/sweep/logs/` — the S0.5 harness
erratum fixed) — the switch's pinned binary (`scripts/ce lem`) vs `./lem`,
each corpus's own invocation: `tests/comprehensive/test_*.lem` one per
invocation with the Makefile's `LEMFLAGS` (56 files + the two joint
invocations = 58), the 12 `tests/backends` `leantests` files (`-wl ign
-lean <file>`), `examples/ppcmem-model` (the root Makefile's 10-file
invocation), `examples/cpp/cmm.lem`. Verbatim:

```
== pinned lem version: Lem 4307dc5
== new lem version:    Lem 4307dc5-dirty
== exit-code comparison (pin vs new); mismatches and both-nonzero listed:
  NONZERO on both: ./backends/coq_test.log pin=1 new=1
  EXIT MISMATCH ./comprehensive/test_fuel_mutual_reader.log: pin=1 new=0
  NONZERO on both: ./cpp.log pin=1 new=1
== per-corpus diff -r verdict (generated trees only):
  comprehensive: DIFFERS (pin 118 / new 120 files) —
Only in …/.tmp/sweep/new/comprehensive/test_fuel_mutual_reader: Test_fuel_mutual_reader_auxiliary.lean
Only in …/.tmp/sweep/new/comprehensive/test_fuel_mutual_reader: Test_fuel_mutual_reader.lean
  backends: IDENTICAL (pin 22 files / new 22 files)
  ppcmem-model: IDENTICAL (pin 20 files / new 20 files)
  cpp: IDENTICAL (pin 0 files / new 0 files)
```

**Verdict: IDENTICAL everywhere; the only difference is the two files
that exist only under the new lem for `test_fuel_mutual_reader.lem`** —
which the pinned lem REFUSES with the guard's text (the negative control;
verbatim, `scripts/ce lem`):

```
File "test_fuel_mutual_reader.lem", line 83, character 18 to line 83, character 74
  Error: Lean backend: 'declare {lean} fuel val' in a mutual block combined with reader lifting (unsupported; extend when needed)
  original input: "match l with | [] -> amb () = 0 | _ :: xs -> rmodd xs end"
```

(`coq_test.lem` and `cmm.lem` fail identically on both lems — the
pre-existing Lean-target refusals recorded in the S0.5 lem-lean record
§4; not this slice's.) Stop rule S2 not triggered.

## 5. Gates (charter §4; verbatim from `.tmp/suite_a2.log`, `scripts/ce make -C tests/comprehensive lean`, `SUITE_DONE rc=0`, wall 357 s)

`./lem -v` at the gated tree (uncommitted): `Lem 4307dc5-dirty`. A first
suite run failed in `lean-compile` on MY Check file only (`Unknown
identifier 'rmev_measure_sufficient'` — it referenced the generated
obligations without importing `Test_fuel_mutual_reader_auxiliary`, the
import `TestFuelMeasureCheck.lean:6` has); the generated module, its
auxiliary and the proofs module had already built. Fixed (one import
line); the run below is the re-run.

- lean-generate: `  OK: test_fuel_mutual_reader.lem` / `=== Generation: 56
  passed, 0 failed, 0 skipped ===` / both `(joint)` OK lines.
- lean-compile: `Build completed successfully (173 jobs).` — inside it,
  the axiom census:
  ```
  info: TestFuelMutualReaderCheck.lean:82:0: 'rping' depends on axioms: [propext]
  info: TestFuelMutualReaderCheck.lean:83:0: 'fping' depends on axioms: [propext]
  info: TestFuelMutualReaderCheck.lean:84:0: 'rmev' depends on axioms: [propext]
  info: TestFuelMutualReaderCheck.lean:85:0: 'rmev_measure_sufficient' depends on axioms: [propext, Quot.sound]
  info: Test_fuel_mutual_reader_lemMeasureProofs.lean:54:0: 'Test_fuel_mutual_reader_lemMeasureProofs.rmev_measure_sufficient' depends on axioms: [propext, Quot.sound]
  info: Test_fuel_mutual_reader_lemMeasureProofs.lean:55:0: 'Test_fuel_mutual_reader_lemMeasureProofs.rmodd_measure_sufficient' depends on axioms: [propext, Quot.sound]
  ```
  (⊆ the trio.)
- lean-panic: `  OK (leg 1): panic prints the Incomplete Pattern message, then continues with default` / `  OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1`
- lean-tuple-once: `  OK: draws: first=1 second=2` / `single-evaluation: OK`
- lean-supply-draws: `  OK: compiled draw sequences hold`
- lean-reader-consumer: `  OK: compiled consumer injection holds`
- lean-reader-multi: `  OK: compiled N-ary seed injection holds`
- lean-fuel-param: `  OK (leg 1): two sufficient fuels agree; insufficient gives the declared sentinel; callee starts from the full ambient` / `  OK (leg 2): loud exhaustion at an insufficient runtime fuel fail-stops (exit 134)`
- **lean-fuel-mutual-reader (new):** `  OK: compiled fuel x reader x mutual composition holds`
- lean-negative: 101 `OK (rejected as declared)` for 101 `negative/neg_*.lem`
  files (derived: 101 − the deleted `neg_fuel_mutual_lifted` + the added
  `neg_fuel_mutual_supply`), 0 FAIL; incl.
  `  OK (rejected as declared): negative/neg_fuel_mutual_supply.lem` and
  `  OK (rejected as declared): negative/neg_supply_mutual.lem`.
- lean-invariance (all ten OK): `  OK: inv_fuel_mutual_reader.lem (7
  artifacts byte-identical across ocaml/hol/isa/coq)`.
- lean-parity: 36 probes — 26 `OK: parity`, 6 `OK: both fail`, 4 `FAIL`
  each paired with its registered `XFAIL` (the D4/X3/F2 deviations;
  derived) — no unregistered failure; the phase passed.
- lean-no-sorry-proofs: `  OK: 11 proofs modules scanned; no
  sorry/admit/axiom/native_decide/bv_decide token` (10 → 11: the new
  proofs module is scanned).
- lean-no-fuel-numerals: `  OK: 260 files scanned; no lemDefaultFuel, no
  LemFuel instance, no literal fuel (F1-F5)`.
- `git diff --stat 4307dc5 -- lean-lib` → empty.

## 6. Docs

`DESIGN.md`: the fuel paragraph gains the composition sentences (fuel ×
truly-mutual; fuel × reader INCLUDING inside a mutual block, the B2
refusal lifted; the remaining refusals supply × truly-mutual and
`reader_seed` × mutual) and the `fuel val` row its composition clause.
`README.md` does not state the refusal — not touched.

## 7. Follow-ups

- **Cerberus (Part B, on the orchestrator's re-launch):** pin bump to
  this commit (the four Lake files + the fork-drift `lem-pin` row + NOTE,
  the S0.5 practice), WIPED regeneration byte-identical to the A0
  snapshot (no fuel'd mutual block is reader-lifted at the current `.lem`,
  so the fix is invisible there), Tier A. Then E-A Phase 1 resumes: the
  two `are_compatible` blocks (`ail/ailTypesAux.lem:784-862`,
  `ctype_aux.lem:283-297`) now generate with the reader binders
  (`digest`, `enum_definitions`, `tagDefs`) on their workers, wrappers and
  obligations — `AilTypesAux_lemMeasureProofs.lean` and
  `Ctype_aux_lemMeasureProofs.lean` are restated there (their statements
  gain the three binders in the generic position; the proofs' shape is
  §3.3's joint induction with inert reader parameters).
- The remaining composition gaps, refused at generation and now probed:
  supply lifting in a truly-mutual block (`neg_fuel_mutual_supply.lem`,
  `neg_supply_mutual.lem`), `reader_seed` in a mutual block (no probe
  pins it; out of this slice's fence — noted).
- Charter erratum: `DESIGN.md` had no sentence stating the refusal to
  reword — the composition sentences are additions (§6).
