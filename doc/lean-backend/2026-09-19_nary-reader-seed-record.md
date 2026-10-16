# N-ary `reader_seed` — record (2026-09-19)

Branch `program-data-parameters` (lem-lean), from mainline `mdd/lean-backend`
@ `f6542f8` (= the cerberus-lean pin: `deps/lem-pinned`, the opam pin, and
every Lake `LemLib` rev). Charter: cerberus-lean
`lean_frontend/docs/2026-09-19_charter-program-data-parameters-S0.5.md`,
Part A (the lem-lean half); the motivating finding is the S0 record
`lean_frontend/docs/2026-09-19_program-data-parameters-S0-record.md` §1.6.
Worker [AGENT] (Fable-class, chartered); rulings quoted with their
provenance; every quoted output is verbatim from this worktree
(`worktrees/lem-lean-program-data-parameters`, logs under its ephemeral
`.tmp/`: `suite_a2.log`, `s05/sweep.log`, `s05/sweep/`); tallies marked
"derived" are derived. Nothing merged, nothing pushed; `lean-lib/` (LemLib)
untouched (`git diff --stat f6542f8 -- lean-lib` → empty); `deps/lem-pinned`
and the shared switch's `lem` untouched (the orchestrator's boundary step).

## 0. Commit

| Commit | Content |
|---|---|
| this commit | the N-ary rule in `src/lean_backend.ml` (seed machinery only); `tests/comprehensive/test_reader_multi.lem` + `lean-test/TestReaderMulti{Impl,Check,Exec}.lean` + lakefile roots/exe + Makefile phase `lean-reader-multi`; `negative/neg_seed_{arity,noreader,nonvar}.lem`; `invariance/inv_reader_multi.lem`; `DESIGN.md` (three sites); this record |

## 1. Rulings and decisions honoured (provenance)

- [USER 2026-09-19] (charter §0): the operator decides the consequential questions and leaves
  implementation-focused calls to the agent; on Q2, agreed to roll the two
  together —
  D-A and E-A are one arc with one consumer re-pin; S0.5 is that arc's
  backend prerequisite.
- [USER 2026-09-04] (S0 record §1.6): the lem structure is not changed for
  OCaml's sake — the rule below changes NO `.lem` in cerberus and no
  non-Lean emitter; the invariance witness (§3.4) is the check.
- [USER 2026-09-08]: nothing new is to be built out of
  policy — one backend rule, its tests/probes, docs, this record;
  no new proof or artefact surface (the kernel pins are plain `rfl`/`decide`
  on concrete values; `#print axioms` on the two named defs is the trio).
- **Q-B, decided [AGENT] by the orchestrator, flagged to the operator**
  (charter §0; S0 record §5 Q-B): **N-ary `reader_seed`** — with N declared
  readers a seed def's first N parameters are the seeds, positionally in
  the GLOBAL SORTED reader order (the one order the lifted binders and the
  consumer stubs already use: `lean_reader_get_params`, sorted by binder
  name). Accepted consequence for cerberus (E-A/D-A, not here):
  `mini_pipeline.lem:70 run_const_expr_driver tds dr_st` becomes
  `run_const_expr_driver <digest> <enum_definitions> tds dr_st` — two
  leading parameters DEAD on the OCaml target, the precedent being the
  supply threading (`mini_pipeline.lem:80-86`: *"On the OCaml target the
  threaded values are DEAD (the mints redirect ambiently)"*;
  `cabs_to_ail.lem:1131-1133` *"DEAD round-trip on the OCaml target"*),
  accepted under the same [USER 2026-09-04] rule. The alternative — a
  partial seed naming the reader it seeds, the def lifted for the rest —
  needs a lifted-AND-seeded def shape the backend has no notion of
  (`lean_backend.ml` "reader_seed defs are never lifted"; "reader_seed def
  unexpectedly reader-lifted" refuses exactly that): two rules instead of
  one. Revisitable by the operator; if reversed, THIS half is what changes.

## 2. The rule and why

### 2.1 The failing case (S0 evidence, verbatim)

Three readers `tagDefs`/`digest`/`enum_defs`, a consumer, and
`seed_entry tds x = uses_three x` declared `reader_seed`
(`2026-09-19_program-data-parameters-S0-evidence/probe/probe_seed3.lem`,
`logs/gen_probe_seed3.log`, `lem -v` → `Lem f6542f8`):

```
File "probe_seed3.lem", line 32, character 24 to line 32, character 35
  Error: Lean backend: reader_seed requires exactly one declared reader
  original input: "uses_three x"
```

In the model this is `mini_pipeline.lem:78` the moment a second
`declare {lean} reader val` lands (`make lean-prelude-src` red).

### 2.2 The guard's concern, and how the association meets it

The guard (`src/lean_backend.ml:4459-4464` at `f6542f8`, verbatim):

```
| Some _ when List.length (get_reader_params ()) <> 1 ->
  (* The seed name overrides EVERY injected reader
     parameter — with more than one reader that would
     silently conflate them (audit finding). *)
  raise (Reporting_basic.err_general true (locn_of_clause_group g)
    "Lean backend: reader_seed requires exactly one declared reader")
```

Its concern was real for the 1-ary machinery: `St.reader_seed_param` held
ONE name, and `reader_inject_name pname` returned that name for EVERY
reader binder — with two readers both injection sites would have received
the same seed. The fix replaces the one name by a per-reader association
(reader binder name → seed parameter name), built positionally over the
sorted reader list; `reader_inject_name` looks the binder up. Each reader
then has its own seed by construction and nothing is conflated — the guard
has no remaining job and is deleted. It had no probe at `f6542f8`
(`grep -rl "exactly one declared reader" tests doc` → nothing); its
successor cases are probed (§3.3).

### 2.3 The rule

`declare {lean} reader_seed val f`, with N declared readers: `f` is not
lifted; its first N parameters are the seeds, one per declared reader,
positionally in the global sorted reader order (sorted by the injected
binder name `_lemReader_<name>`, i.e. by the reader's unqualified name —
`lean_reader_get_params`); inside `f`'s body every injection site (lifted
callee call, consumer call, applied reader read, bare reader reference)
receives the seed associated with ITS reader instead of that reader's
binder. The seeds are referenced by name, so each seed position must be a
simple variable. N = 1 is the old rule exactly (§4: byte-identical output
on every existing program).

### 2.4 The refusals

New, fail-closed:

- fewer than N parameters →
  `Lean backend: reader_seed def must take N seed arguments (one per declared reader, in the global sorted reader order: <names>)`
  (probe: `neg_seed_arity.lem`, the S0 shape — fragment
  `reader_seed def must take`);
- no reader declared →
  `Lean backend: reader_seed declared but no reader is declared (nothing to seed)`
  (probe: `neg_seed_noreader.lem`; the old guard refused this shape too,
  as 0 ≠ 1, without naming the reason);
- reworded to the plural: a seed position that is not a simple variable →
  `Lean backend: reader_seed def's seed arguments must be simple variables (argument i of N, the seed for reader <name>, is not)`
  (probe: `neg_seed_nonvar.lem`; was "reader_seed def's first argument must
  be a simple variable" — no probe pinned the old wording).

Unchanged: the multi-clause/mutual, instance and fuel refusals, the
reserved-binder check (`_lemReader_*`), "reader_seed def unexpectedly
reader-lifted", the RC-mix and supply×reader_seed guards.

### 2.5 Implementation (`src/lean_backend.ml` at this commit; seed machinery only)

- `St.reader_seed_param : (string * string) list option ref` (`:351`;
  header comment states the N-ary rule; lifetime class [render]
  unchanged; reset `:434` textually unchanged).
- `seed_info` (`:4470-4501`): `readers = get_reader_params ()`, `n`; the
  `n = 0` and `List.length pats < n` refusals; the first `n` clause
  patterns (`List.filteri`) paired positionally with `readers`
  (`List.combine`), each `P_var`/`P_var_annot` → `(binder, seed)`, else
  the plural refusal naming position and reader. The `<> 1` guard is
  deleted; `Some _ when is_truly_mutual` (`:4503`) and the following arms
  are as before.
- `reader_inject_name pname` (`:3182-3192`): `None` → `pname` (the
  lifted-binder case); `Some assoc` → `List.assoc_opt pname assoc`; a miss
  inside a seed def is an internal invariant violation and raises
  (fail-closed — the association is total over `get_reader_params ()` by
  construction, and a non-lifted seed def has no binder to fall back to).
- `reader_consumer_scope_check` (`:3167`, reads `<> None`) and the
  save/restore (`:4597-4599`) adapt with no textual change (the type
  changed under them); the comment at `:1194-1196` ("never lifted") and
  the scope-check comment reworded to the plural.
- The three injection sites are untouched by design and confirmed to
  route through `reader_inject_name`: `reader_args_output` (`:3194-3197`,
  consumer call sites — every reader), the applied reader read (`:5857`),
  the bare reader reference (`:5975`, eta-expanded).
- Nothing else: no grammar change, no change to lifting, to the other
  emitters, or to `lean-lib/`. Build: `scripts/ce make` at the root — zero
  warnings attributed to `lean_backend.ml` (the build log's warnings are
  the pre-existing ones in other files; checked by file attribution).

### 2.6 Observations (pre-existing behaviour, unchanged; for the record)

- A type-ANNOTATED seed variable `(cv : nat)` is refused: in lem's typed
  AST a source-level `(x : t)` pattern is `P_typ`, not `P_var_annot`, so
  the `P_var | P_var_annot` arms never see it. Pre-existing — the pinned
  lem refuses the one-reader probe `let seed1 (cv : nat) x = uses_cfg x + cv`
  identically (verbatim, pinned then new):
  ```
  File "probe_annot1.lem", line 8, character 26 to line 8, character 40 processed by: inline_exp_macro, inline_exp
    Error: Lean backend: reader_seed def's first argument must be a simple variable
    original input: "uses_cfg x + cv"
  ```
  ```
  File "probe_annot1.lem", line 8, character 26 to line 8, character 40 processed by: inline_exp_macro, inline_exp
    Error: Lean backend: reader_seed def's seed arguments must be simple variables (argument 1 of 1, the seed for reader cfg, is not)
    original input: "uses_cfg x + cv"
  ```
  Not changed here (the charter names the two accepted arms; the message
  says what to write instead).
- Tuple, literal and constructor patterns in a seed position never reach
  the check: lem's pattern compiler rewrites such a head into a fresh
  variable plus a body `match` first (observed: `let seed2 av (b1, b2) x`
  → `def seed2 (av : Nat) (p : Nat × Nat) (x : Nat) := match av, p, x with
  | av, (b1, b2), x => …` with `p` the seed). Semantics preserved — the
  seed is the whole argument; a type mismatch against the reader's type is
  Lean's build-time error, as for the 1-ary rule (the backend never
  checked a seed's type against its reader). A wildcard `_` does reach the
  check and is refused (it has no name) — the `neg_seed_nonvar` shape.

## 3. Tests

### 3.1 `test_reader_multi.lem` (+ `TestReaderMultiImpl.lean`)

Three readers DECLARED `gamma : unit -> nat`, `alpha : unit -> nat`,
`beta : unit -> string` — sorted order `alpha, beta, gamma` differs from
declaration order, and `alpha`/`gamma` share a type so a positional
mix-up type-checks and is caught only by value. Consumer `combine` →
`TestReaderMultiImpl.combine (alpha : Nat) (beta : String) (gamma : Nat) (x : Nat) := alpha * 1000 + beta.length * 100 + gamma * 10 + x`.
Lifted defs reading one (`uses_one`), two (`uses_two`), all three
(`uses_three`) readers and the consumer (`uses_combine`); a supply-lifted
def in the same reader cone (`tick` supply, `draws_and_reads`); the seed
def `seed3 av bv gv x = combine x + uses_three (x + 1) + uses_two (x + 2)`
(consumer directly AND two lifted callees); a supply-lifted seed def
`seed3_draws av bv gv x = draws_and_reads x`; the seed-rooted, non-lifted
`via_seed3 x = seed3 7 "ab" 9 x` asserted from the `.lem`
(`assert rm_seed_ok : (via_seed3 3 = 8110)`). Expected values, by hand:
seeds alpha=7, beta="ab", gamma=9, x=3: `combine 3 = 7293`,
`uses_three 4 = 733`, `uses_two 5 = 84`, total 8110; under an alpha/gamma
swap 9273 + 931 + 102 = 10306.

Generated shape (verbatim `def` heads, new `./lem`):

```
def  uses_three (_lemReader_alpha : Nat) (_lemReader_beta : String) (_lemReader_gamma : Nat)  (x : Nat)  : Nat :=  (((_lemReader_alpha  *   100)  +  (String.length  (_lemReader_beta)  *   10))  + _lemReader_gamma)  +  x
def  uses_combine (_lemReader_alpha : Nat) (_lemReader_beta : String) (_lemReader_gamma : Nat)  (x : Nat)  : Nat := ( TestReaderMultiImpl.combine _lemReader_alpha _lemReader_beta _lemReader_gamma)  x
def  draws_and_reads (_lemReader_alpha : Nat) (_lemReader_beta : String) (_lemReader_gamma : Nat) (_lemSupply_tick : Nat)  (x : Nat)  : ((Nat) × Nat) := 
def  seed3  (av : Nat) (bv : String) (gv : Nat) (x : Nat)  : Nat :=  ((TestReaderMultiImpl.combine av bv gv)  x  + ( uses_three av bv gv)  (x  +   1))  + ( uses_two av bv gv)  (x  +   2)
def  seed3_draws (_lemSupply_tick : Nat)  (av : Nat) (bv : String) (gv : Nat) (x : Nat)  : ((Nat) × Nat) := 
def  via_seed3  (x : Nat)  : Nat :=  seed3 (  7)  "ab" (  9)  x
```

(binder order `[Inhabited]`, readers sorted, supply, own args; a
supply-lifted seed def is `[supply] [seeds] [own args]`, as `seeded` in
`test_supply.lem`.)

### 3.2 `TestReaderMultiCheck.lean` (kernel) and `TestReaderMultiExec.lean` (compiled, phase `lean-reader-multi`)

Check: signature pins for every lifted def (`Nat → String → Nat → …`) and
the binder NAMES through named arguments
(`uses_one (_lemReader_alpha := 7) (_lemReader_beta := "ab") (_lemReader_gamma := 9) 3 = 12`,
likewise `draws_and_reads` with `_lemSupply_tick`, `seed3 (av := …)`,
`seed3_draws (_lemSupply_tick := 40) (av := …)`); `seed3` NOT lifted;
`rfl` value pins `uses_two 7 "ab" 9 3 = 82` (would read 100 under the
declaration order), `uses_combine 7 "ab" 9 3 = 7293` / `… 9 "ab" 7 3 = 9273`
and `≠` by `decide`; the seed pickup `seed3 7 "ab" 9 3 = 8110` (the pin
that FAILS under an alpha/gamma seed swap: 10306), decomposed as
`uses_combine … + uses_three … 4 + uses_two … 5`; `via_seed3 3 = 8110`;
seed × supply `seed3_draws 40 7 "ab" 9 3 = (7333, 41) = draws_and_reads 7 "ab" 9 40 3`;
`#print axioms via_seed3` / `uses_three`. Exec: the same eight facts in a
compiled binary (`reader_multi: OK`). Lakefile: roots `Test_reader_multi`,
`Test_reader_multi_auxiliary`, `TestReaderMultiImpl`, `TestReaderMultiCheck`;
`lean_exe «test-reader-multi»` (root `TestReaderMultiExec`). Makefile:
phase `lean-reader-multi` modelled on `lean-reader-consumer`, in the `lean:`
list after it and in `.PHONY`.

### 3.3 Negative probes (verbatim rejections, new `./lem`)

```
File "negative/neg_seed_arity.lem", line 27, character 24 to line 27, character 35
  Error: Lean backend: reader_seed def must take 3 seed arguments (one per declared reader, in the global sorted reader order: digest, enum_defs, tagDefs)
  original input: "uses_three x"
```
```
File "negative/neg_seed_noreader.lem", line 13, character 17 to line 13, character 23
  Error: Lean backend: reader_seed declared but no reader is declared (nothing to seed)
  original input: "plain x"
```
```
File "negative/neg_seed_nonvar.lem", line 26, character 20 to line 26, character 30
  Error: Lean backend: reader_seed def's seed arguments must be simple variables (argument 2 of 2, the seed for reader beta, is not)
  original input: "uses_both x"
```

`neg_seed_arity` is the S0 failing shape (`seed_entry tds x` with readers
`tagDefs`/`digest`/`enum_defs`), now refused by the arity rule. A first
draft of `neg_seed_nonvar` used a tuple pattern and was ACCEPTED (§2.6:
desugared before the check) — the committed probe uses a wildcard.

### 3.4 Invariance witness

`invariance/inv_reader_multi.lem`: the multi test's shape with lem bodies
for the rep'd vals; the `{lean}` declares stripped must leave the
ocaml/hol/isa/coq output byte-identical (suite line, §5).

### 3.5 Regression control

`test_reader_consumer.lem`, `TestReaderConsumerCheck.lean`,
`TestReaderConsumerExec.lean`, `neg_rc_*`, `neg_fuel_reader_seed.lem`,
`neg_supply_mix_seed.lem`, `inv_reader_consumer.lem`, `test_supply.lem`
§6 (`seeded`) — all UNCHANGED and green (§5).

## 4. The A3 byte-identity sweep (pinned `Lem f6542f8` vs new `./lem`)

Method (`.tmp/s05/sweep.sh`, ephemeral): for each corpus, generate Lean
output twice into scratch trees under `.tmp/s05/sweep/{pin,new}/` — with
the switch's pinned binary (`scripts/ce lem`) and with the worktree's
`./lem` — using each corpus's own invocation, then `diff -r`:

- `tests/comprehensive/test_*.lem`: one file per invocation with the
  Makefile's `LEMFLAGS` (`-wl ign -i ../../library/pervasives.lem -lean`),
  55 files, plus the two joint invocations of `lean-generate`
  (`test_cross_recup_base.lem test_cross_recup_import.lem`;
  `test_cross_field_access.lem test_cross_field_access_import.lem`) — 57
  invocations;
- `tests/backends`: the 12 files of the Makefile's `leantests` target with
  its invocation (`../../lem -wl ign -lean <file>`);
- `examples/ppcmem-model`: the root `Makefile:111-123` 10-file invocation;
- `examples/cpp/cmm.lem`: `../../lem -wl ign -lean cmm.lem`.

Versions (verbatim): `== pinned lem version: Lem f6542f8`,
`== new lem version:    Lem f6542f8-dirty`.

Erratum to my own script: it wrote the per-invocation `.log` files INSIDE
the diffed trees, so the first `diff -r` pass reported those logs
(`pin_exit=` vs `new_exit=` and `scripts/ce`'s env banner) — noise from
the harness, not from lem. The verdict below is the re-diff of the same
generated trees with the logs excluded (`diff -r -x '*.log'`):

```
  comprehensive: DIFFERS —
Only in .tmp/s05/sweep/new/comprehensive/test_reader_multi: Test_reader_multi_auxiliary.lean
Only in .tmp/s05/sweep/new/comprehensive/test_reader_multi: Test_reader_multi.lean
  backends: IDENTICAL (22 files new / 22 files pin)
  ppcmem-model: IDENTICAL (20 files new / 20 files pin)
  cpp: IDENTICAL (0 files new / 0 files pin)
```

Per-corpus generated file counts (measured, logs excluded):
comprehensive pin=116 new=118; backends 22/22; ppcmem-model 20/20;
cpp 0/0. **Verdict: IDENTICAL everywhere; the only difference is the two
files that exist only under the new lem for `test_reader_multi.lem`** —
the file the pinned lem REFUSES (the negative control showing the rule is
load-bearing; verbatim, `scripts/ce lem`):

```
File "test_reader_multi.lem", line 81, character 30 to line 81, character 46
  Error: Lean backend: reader_seed requires exactly one declared reader
  original input: "draws_and_reads x"
```

(the location is `seed3_draws`, not `seed3`: defs render last-to-first.)
Exit-code comparison over every invocation: the only mismatch is
`test_reader_multi` (pin=1 new=0). Stop rule S2 not triggered.

Two corpus files fail IDENTICALLY on both lems (exit 1 on both, error
text identical modulo `scripts/ce`'s banner) — pre-existing at the pin,
independent of this slice, noted for the orchestrator:

```
no location information available
  Error: Lean backend: cannot derive BEq/Ord instances for type 'v': heterogeneous type-parameter counts put its mutual block in the Type 1 universe (the historical sorry-bodied residual instances are deleted, arc-10 audit fix); escape hatches: 'declare {lean} skip_instances type v' plus hand-written Lean instances where demanded, or 'declare lean target_rep type v' mapping it to a hand-written Lean type
```
(`tests/backends/coq_test.lem`)
```
no location information available
  Error: Lean backend: cannot derive an Inhabited instance for type 'tid' (no constructor with derivably-inhabitable fields), but generated code demands one; escape hatches: 'declare {lean} skip_instances type tid' plus a hand-written Lean instance, or 'declare lean target_rep type tid' mapping it to a hand-written Lean type
```
(`examples/cpp/cmm.lem`) — i.e. the `tests/backends` `leantests` and the
root `lean-tests` targets are not green at `f6542f8` either; the
comprehensive suite (the normative gate, §5) is.

## 5. Gates (charter §4; verbatim tails from `.tmp/suite_a2.log`, `scripts/ce make -C tests/comprehensive lean`, exit 0)

`./lem -v` at the gated tree (uncommitted): `Lem f6542f8-dirty`.

- lean-generate:
  ```
    OK: test_reader_multi.lem
  === Generation: 55 passed, 0 failed, 0 skipped ===
    OK: test_cross_recup_base.lem + test_cross_recup_import.lem (joint)
    OK: test_cross_field_access.lem + test_cross_field_access_import.lem (joint)
  ```
- lean-compile: `Build completed successfully (169 jobs).` — with the
  axiom census inside it:
  ```
  info: TestReaderMultiCheck.lean:69:0: 'via_seed3' depends on axioms: [propext, Classical.choice, Quot.sound]
  info: TestReaderMultiCheck.lean:70:0: 'uses_three' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
  (= the trio; charter §4 "the trio or fewer").
- lean-panic:
  ```
    OK (leg 1): panic prints the Incomplete Pattern message, then continues with default
    OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1
  ```
- lean-tuple-once: `  OK: draws: first=1 second=2` / `single-evaluation: OK`
- lean-supply-draws: `  OK: compiled draw sequences hold`
- lean-reader-consumer: `  OK: compiled consumer injection holds`
- lean-reader-multi (new): `  OK: compiled N-ary seed injection holds`
- lean-fuel-param:
  ```
    OK (leg 1): two sufficient fuels agree; insufficient gives the declared sentinel; callee starts from the full ambient
    OK (leg 2): loud exhaustion at an insufficient runtime fuel fail-stops (exit 134)
  ```
- lean-negative: 101 `OK (rejected as declared)` lines for 101
  `negative/neg_*.lem` files (derived: 98 + the 3 new), no FAIL; the new
  three:
  ```
    OK (rejected as declared): negative/neg_seed_arity.lem
    OK (rejected as declared): negative/neg_seed_nonvar.lem
    OK (rejected as declared): negative/neg_seed_noreader.lem
  ```
- lean-invariance (all nine OK; the two reader witnesses):
  ```
    OK: inv_reader_consumer.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
    OK: inv_reader_multi.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
  ```
- lean-parity: 36 probes — 26 `OK: parity …`, 6 `OK: both fail …`, and 4
  `FAIL` lines each followed by its `XFAIL (expected, registered)` line
  (the registered D4/X3/F2 deviations; derived counts) — no unregistered
  failure; the phase passed (the suite continued and exited 0).
- lean-no-sorry-proofs:
  `  OK: 10 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token`
- lean-no-fuel-numerals:
  `  OK: 257 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)`
- `SUITE EXIT=0`
- `git diff --stat f6542f8 -- lean-lib` → empty.

## 6. The A0 before-snapshot (cerberus side; Part B's reference)

Taken FIRST, before any lem-lean edit, in
`worktrees/cerberus-lean-arc/program-data-parameters` (branch
`arc/program-data-parameters` @ `d5a1025ff`): `scripts/ce lem -v` →
`Lem f6542f8`; `scripts/ce make prelude-src lean-prelude-src` (the sync
stamps re-recorded to the same content: `git status` clean after);
`find ocaml_frontend/generated lean_frontend/generated -type f | sort | xargs sha256sum`
→ `.tmp/s05/gen-before.sha256`, **305 files** (86 under
`ocaml_frontend/generated` + 219 under `lean_frontend/generated`;
derived split). Extra, separate file (not required by the charter):
`.tmp/s05/gen-before-sibylfs.sha256`, 16 files of `sibylfs/generated`
(also lem-generated).

## 7. Follow-ups and errata

- **Part B (cerberus, on the orchestrator's re-launch):** Lake pin bump to
  this commit's full hash (the `be1cebe36` file set), `make prelude-src
  lean-prelude-src` with the rebuilt switch `lem`, hash-list diff against
  `.tmp/s05/gen-before.sha256` EMPTY (the model declares one reader
  today, so the fixed backend must emit byte-for-byte what the pinned one
  emits — §4 is the lem-side evidence), lem-sync checks passing without
  re-record, Tier A.
- **E-A/D-A (the consumer of this rule):** `run_const_expr_driver` gains
  two leading seed parameters in the `.lem` (sorted order `digest`,
  `enum_definitions`, `tagDefs`); `fork_drift_manifest.txt` re-pin
  foreseen there (S0 record §1.6).
- Charter errata: `DESIGN.md:240-241` ("readers and `reader_seed`
  compose …") carries no 1-ary wording — not edited; the paragraph at
  `:259-260` and the row at `:505` did and are reworded; the
  `reader_consumer` paragraph's test list gains the multi family.
  `README.md` states no 1-ary rule — not touched.
- The sweep harness erratum (§4): logs inside the diffed trees; the
  verdict is the log-excluded re-diff of the same outputs.
- The two pre-existing Lean-target refusals in the non-comprehensive
  corpora (§4, `coq_test.lem`, `cmm.lem`) — identical on both lems, not
  this slice's; flagged.
