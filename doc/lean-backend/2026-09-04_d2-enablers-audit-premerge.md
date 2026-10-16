# Pre-merge audit — `arc/d2-enablers` @ `22aa0fb` (2026-09-04)

Auditor [AGENT] (independent of the worker and of the orchestrator's
concurrent re-verification), worktree
`worktrees/lem-lean-audit/d2-enablers-premerge`, branch
`audit/d2-enablers-premerge` (this document is its only commit). Range
audited: `742506d..22aa0fb` (2 commits: `df19cb1` code + tests, `22aa0fb`
the record). Read in full: `2026-09-04_d2-enablers-record.md`,
`2026-09-04_fuel-measure-record.md` §2, `2026-09-04_structural-declare-record.md`
§6.1, `DESIGN.md`, `doc/manual/backend_lean.md`, `TODO.md`, the diff.
Every quoted output below is verbatim from this worktree (`.tmp/` is
ephemeral, deleted at slice end; log names given); counts labelled
"derived" are derived. Nothing merged, nothing pushed; `deps/`, the
cerberus checkouts and the arc worktree were read only.

## 0. Verdict

**MERGEABLE (ff-only, on operator sign-off) — no MAJOR finding.** 3 MINOR
(all documentation-vs-behaviour accuracy; the behaviour in each case is
fail-closed), 8 NOTEs. What holds, measured here and not taken from the
record: the OCaml output is byte-identical three ways on the full cerberus
tree (86 files: lem `3c88f0d` on the original sources = this lem on the C1
sources + the three new declares = the primary checkout's generated tree);
every emitted size function is `termination_by structural`, kernel-computable
(`decide` on closed terms) and axiom-free on 4.28.0 and 4.32.2; the
refusals fire (11 refusal probes, 6 of them new here); the fuel-lifted
inductive parameter is accepted by Lean 4.32.2 and 4.28.0; the suite is
green (`EXIT 0`, 10:22), the non-Lean net is green; the record's tallies
reproduce within derived-count noise.

## 1. Findings (MAJOR → MINOR → NOTE)

No MAJOR.

### MINOR-1 — a type recursive ONLY through an unsupported head is refused as "non-recursive" (wrong reason, right refusal)

`src/lean_backend.ml`, `lean_size_block`: `recursive` is "some field's
`lean_size_shape` is not `CSleaf`", and every unsupported head is a leaf,
so a type that recurses only through a user type / `set` is classified
`Error "a non-recursive type (its size is the constant 1 — a measure over it
would be a magic value; measure the data that actually decreases)"`.
Probe `.tmp/probes/adv_tb_measure.lem` (`type box 'a = Box of list 'a`,
`type tb = TL | TB of box tb`, `fuel_measure val tbcount = `lemSize t``),
verbatim:

```
  Error: Lean backend: the fuel measure of tbcount uses `lemSize t`, but the type of t (Adv_tb_measure.tb) has no derived size function (FM-size-type: it is a non-recursive type (its size is the constant 1 — a measure over it would be a magic value; measure the data that actually decreases)); a size is derived for every recursive block of generated inductive types in a user module (`t.lemSize`)
```

(same for `type sf = SE | S of set sf`, `adv_fn_field.lem`). The refusal is
correct — no size the derivation can build bounds this recursion — but
the reason is false (`tb` IS recursive) and the advice ("measure the data
that actually decreases") points nowhere: there is no measurable
parameter. Fix (one string, one flag): distinguish "no field reaches a
sibling" from "every reaching field is under an unsupported head (`box`,
`set`, another block's type) — the derivation cannot count it; write a
hand-written size (`declare {lean} extra_import`) or add cross-head counting
(TODO row 15)". Not blocking: no cerberus census row has this shape (the
81 derived types were generated; the three measured sites resolve).

### MINOR-2 — the target_rep'd-type reason claimed by the record/manual is not the one emitted

Record §2.1 and the manual: "library/target_rep'd/opaque/Type-1-block
types — the census carries the reason and the message names it" (the code
has the string `"a type with a Lean target_rep (rendered as an abbrev of a
hand-written type)"`). Probe `adv_neg_reptype.lem` (`type rt = RL | RN of
list rt`, `declare lean target_rep type rt = `Nat``, `lemSize r`), verbatim:

```
  Error: Lean backend: the fuel measure of rspin uses `lemSize r`, but the type of r (Adv_neg_reptype.rt) is not a generated inductive type of this invocation (FM-size-type: no derived size function exists for it — a size is derived for every recursive block of generated inductive types in a user module)
```

— the census has NO entry for `rt` (the `None` branch), not `Size_none
"a type with a Lean target_rep …"`. Fail-closed either way; the documented
reason string is unreachable for this case as far as this probe shows (the
Type-1 reason IS reached: `adv_type1.lem` → "it is a member of a
heterogeneous (indexed, Type 1) mutual block"; the library reason is
unreachable by construction — a `list nat` parameter gives the same `None`
message, `adv_neg_libtype.lem`). Not diagnosed why (out of budget); fix is
either to register target_rep'd type defs in `lean_size_prepass` or to
amend the two sentences.

### MINOR-3 — the manual now says a `lemma` referencing fuel is refused; lemmas are dropped, not refused (pre-existing behaviour, new wrong sentence)

`doc/manual/backend_lean.md` (this diff): "a fuel-declared or fuel-lifted
definition referenced where no `[LemFuel]` is in scope — a lem `assert`, a
lemma (`neg_fuel_scope_assert`; …)". Measured (`adv_indreln_lemma.lem`:
`lemma reach_self : (forall n. reach n n)` on a fuel-lifted relation): lem
exit 0, and the Lean output is

```
/- removed theorem  reach_self -/
```

— the Lean backend renders every `lemma`/`theorem` as a removed comment
(`src/lean_backend.ml:3109-3114`, pre-existing), so nothing is refused and
nothing is emitted. Not a fail-open path (no Lean artifact carries the
reference), but the sentence is false. Fix: "a lem `assert` (a lem
`lemma`/`theorem` is not emitted by this backend at all)".

### NOTE-1 — `lemSize` is now a reserved word inside measures; a PARAMETER of that name is refused with the FM-size-param wording

`adv_param_named_lemSize.lem` (`let rec spin lemSize n = …`, measure
`lemSize + n + 1`), verbatim: "`lemSize` in the fuel measure of spin must be
applied directly to one of the parameters lemSize, n (FM-size-param …)".
Fail-closed and harmless (rename the parameter), but the message lists
`lemSize` among the parameters it says cannot be used. Worth one clause in
the manual's reserved-names sentence.

### NOTE-2 — the leaf-0 choice (record §6 item 1), assessed: irrelevant for type variables, and NOT the mechanism that makes a size insufficient

The record is right that a type-variable leaf's weight does not affect the
bound: a lem `let rec` is monomorphic, so one recursion cannot descend into
an `'a` field (instantiated to the type itself or not); another function's
recursion into it has its own counter (its own measure or the ambient).
Probe: `rose.lemSize (Rose (RR (Rose RL [Rose RL []])) []) = 1` by `decide`
— the whole inner rose is one leaf, and `rcount` (which walks only the
outer rose) is correctly measured. What DOES make a derived size
insufficient is a field under an unsupported head (`box tc`, `set t`,
another block's type) that the SAME recursion descends into — the record
names this and points to the obligation. Exhibited (`adv_param_recpos.lem`,
`type tc = TCL | TC of list tc * box tc`, `tcc` walks both; `AdvCheck.lean`,
4.28.0, verbatim from the build):

```
example : tc.lemSize (TC [] (Box [TCL])) = 1 := by decide
example : tcc_lemFuel 2 (TC [] (Box [TCL])) = 2 := by decide          -- the true value
info: AdvCheck.lean:61:0: 2
info: AdvCheck.lean:62:0: lem: fuel exhausted
backtrace:
info: AdvCheck.lean:62:0: 1
```

(the second `#eval` is the wrapper `tcc` at the derived size 1: the inner
call exhausts — loud at runtime — and the value sentinel `0` yields 1.) The
obligation `tcc_measure_sufficient` at this term is `2 = 1 + fuelExhausted
0` with an OPAQUE sentinel (`opaque fuelExhaustedWith`, `LemLib.lean:190-191`),
so it is unprovable without an axiom about the sentinel — the design's
backstop holds exactly where the record says. Two consequences for the
consumer, not for this slice: (a) leaf 0 vs 1 is cosmetic; keep 0
([AGENT] concurs with the record's choice); (b) the backstop is the
AUXILIARY module's build, and the record's own §4.4 scratch build shows
the skip is possible at the package level (three auxiliary roots dropped) —
cerberus's `scripts/check_lakefile_roots.sh` (C1 WIP) should be confirmed
to require every `_auxiliary` root before C1 claims green.

### NOTE-3 — record integrity: tallies reproduce within derived-count noise; one line number off by one

Regenerated here (this lem, `frontend-c1d`, 170 files; derived `grep`):
`[LemFuel]` binders **397** (record 397); ambient wrappers **64** (64);
measured wrappers **3** (3); size functions **81** types (81), **66**
helpers (66), **27** blocks (27); size blocks **1052 lines** (1052),
**55229 bytes** (record 55205 — a block-boundary convention; mine includes
the `end` line); tree **39110 lines** (39110), **3566329 bytes** (record
3553252, 0.37% apart — method not stated in the record; the ratio is 1.55%
vs the record's 1.6%, same rounding class). `inductive` lines 292 = 290
data types + 2 Prop relations (`Cmm_op.lean`: `incTrace`, `monTrace`) —
consistent with "290 inductives". Checklist §4.1/§4.5: the third declare is
appended to a 469-line file, so it is `defacto_memory_aux.lem:470`, not
`:469` (`ctype.lem:428`, `core.lem:473` are right). Nothing here would
block C1.

### NOTE-4 — C1 checklist (§4.5) verified item by item against the WIP tree

(1) the five numeric declares are gone in `wip/fuel-parameter-C1-scratch`
(`driver.lem` −9 lines, `nondeterminism.lem` −6, `git diff 1b57bcf26`);
(2) exactly 19 `declare {lean} fuel_consumer val` lines added to `mem.lem`
(counted); (3) the three `fuel_measure` lines generate (below); (4)
`Cmm_op.lean:411` `inductive monTrace  [LemFuel] : …` from the unchanged
source; (5) the obligation is emitted exactly as quoted
(`Ctype_auxiliary.lean:45-47`, `import Ctype_lemMeasureProofs` at line 6;
likewise `Core_auxiliary`, `Defacto_memory_aux_auxiliary`). The record's
"`c` is `ctypeEqual`'s first parameter after pattern compilation" is
confirmed: `Ctype.lean:442: def ctypeEqual (c : ctype) (c0 : ctype) : Bool
:= ctypeEqual_lemFuel (ctype.lemSize c) c c0`.

### NOTE-5 — pre-existing limitations met while probing (not this slice's, not worsened by it)

A non-uniform datatype (`type nest 'a = NLeaf of 'a | NNode of nest (list
'a)`) generates but the `inductive` itself fails in Lean (the size function's
`Unknown identifier nest` errors are downstream of that); a relation used as
a `bool` in a definition (`let uses_reach n = reach n n`) renders `Prop`
where `Bool` is expected. Both pre-exist `df19cb1`; the size emission and
the inductive parameter add no failure of their own.

### NOTE-6 — invariance-harness artifact (not a defect of this slice)

Stripping `declare {lean}` lines from a probe whose `assert` FOLLOWS them
shifts the assert's source line, which the OCaml auxiliary records as a
string (`run_test "mreach_ok" "File …, line 34 …"` vs `line 31`) — the
suite's `lean-invariance` phase would report that as "non-Lean output
changed" for such a probe. None of the six suite witnesses has that shape;
the record's invariance claims stand. Worth a comment in the harness.

### NOTE-7 — the baseline-binary version stamp is stale (context for future auditors)

`deps/lem-pinned/lem -v` prints `Lem 3c88f0d` although the source and the
`_build/main.native` (mtime 2026-09-04 03:01) are `742506d` — the version
string is minted at build time from the enclosing HEAD and is not a
reliable identity (the record's §4.1 caveat, generalised). The baseline
used here was built from `git archive 3c88f0d` (source diff against `git
show 3c88f0d:src/lean_backend.ml` empty; its `-v` prints `Lem 22aa0fb`,
this worktree's HEAD, for the same reason).

### NOTE-8 — the `od`/`ev` mutual relation block renders in reverse source order

`adv_indreln.lem` declares `ev` then `od`; the output is `inductive od …`
then `inductive ev …` inside one `mutual`. Semantically inert (Lean's
mutual block); pre-existing gathering order, not touched by this diff.

## 2. What was run — verbatim

### 2.1 Build, suite, net (this worktree, lem `22aa0fb`)

`make` → `EXIT 0` (28.5s). `tests/nonlean-regress/run.sh` (`.tmp/nonlean.log`):

```
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
./tests/nonlean-regress/run.sh  153.48s user 7.60s system 99% cpu 2:41.21 total
EXIT 0
```

`tests/comprehensive`: `make clean` then `make lean`, `CERB_MEM_MAX=16G`
through `capped` (`.tmp/suite.log`), nothing else of mine on the box during
the run (the orchestrator's run was concurrent in its own worktree):

```
=== Generation: 52 passed, 0 failed, 0 skipped ===
info: Test_lem_size_lemMeasureProofs.lean:211:0: 'Test_lem_size_lemMeasureProofs.tm_sum_measure_sufficient' depends on axioms: [propext, Quot.sound]
info: Test_lem_size_lemMeasureProofs.lean:212:0: 'Test_lem_size_lemMeasureProofs.tm_eq_measure_sufficient' depends on axioms: [propext, Quot.sound]
info: Test_lem_size_lemMeasureProofs.lean:213:0: 'Test_lem_size_lemMeasureProofs.mcount_measure_sufficient' depends on axioms: [propext, Quot.sound]
info: Test_lem_size_lemMeasureProofs.lean:214:0: 'Test_lem_size_lemMeasureProofs.sb_count_measure_sufficient' depends on axioms: [propext, Quot.sound]
info: Test_lem_size_auxiliary.lean:35:0: PASS: tm_sum_ok
info: Test_lem_size_auxiliary.lean:39:0: PASS: tm_eq_ok
info: Test_lem_size_auxiliary.lean:43:0: PASS: tm_neq_ok
info: Test_lem_size_auxiliary.lean:47:0: PASS: sz_ok
info: Test_lem_size_auxiliary.lean:51:0: PASS: mcount_ok
info: Test_lem_size_auxiliary.lean:55:0: PASS: sb_count_ok
info: TestLemSizeCheck.lean:30:0: 'tm.lemSize' does not depend on any axioms
info: TestLemSizeCheck.lean:31:0: 'r1.lemSize' does not depend on any axioms
info: TestLemSizeCheck.lean:32:0: 'sbox.lemSize' does not depend on any axioms
info: TestLemSizeCheck.lean:33:0: 'mtree.lemSize' does not depend on any axioms
Build completed successfully (156 jobs).
  OK (leg 1): panic prints the Incomplete Pattern message, then continues with default
  OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1
single-evaluation: OK
  OK: compiled draw sequences hold
  OK: compiled consumer injection holds
  OK (leg 1): two sufficient fuels agree; insufficient gives the declared sentinel; callee starts from the full ambient
  OK (leg 2): loud exhaustion at an insufficient runtime fuel fail-stops (exit 134)
  OK: inv_fuel.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_fuel_measure.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_lem_size.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_reader_consumer.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_structural.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_supply.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: 6 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
  OK: 242 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make lean  646.49s user 70.52s system 115% cpu 10:22.08 total
EXIT 0
```

Derived counts from the same log: 78 × `OK (rejected as declared)` (the 6
new probes among them: `neg_fuel_indreln_scope`, `neg_lem_size_ctor_collision`,
`neg_lem_size_field_collision`, `neg_lem_size_nonind`, `neg_lem_size_nonrec`,
`neg_lem_size_notparam`); parity 24 × `OK: parity`, 6 × `OK: both fail`, 4 ×
XFAIL (`f_int32_overflow`, `f_int_of_big_num`, `p_str_bytes`, `p_str_escapes`
— the registered four). All match the record §5.1.

### 2.2 OCaml byte-identity on the cerberus tree (`.tmp/cerb/gen-run.log`)

Sources (read-only copies): `frontend-orig` = cerberus primary `git archive
1b57bcf26 frontend`; `frontend-c1` = `frontend-orig` with `mem.lem`,
`driver.lem`, `nondeterminism.lem` from `wip/fuel-parameter-C1-scratch`
(`git show`, from the `zero-discrepancy` worktree, read-only); `frontend-c1d`
= `frontend-c1` + the three checklist lines appended (`ctype.lem:428`,
`core.lem:473`, `defacto_memory_aux.lem:470`). Lists/flags from the cerberus
Makefile via `make --eval` (`LEM_SRC` 86 files; `-wl ign -wl_rename warn
-wl_pat_red err -wl_pat_exh warn -cerberus_pp`), the Makefile's four `sed`
patches applied to every output tree so the primary's tree is comparable.
Baseline lem: `.tmp/lem-base`, built from `git archive 3c88f0d` (source
check: `diff <(git show 3c88f0d:src/lean_backend.ml) src/lean_backend.ml`
empty). A first attempt with zsh word-splitting produced EMPTY trees and a
vacuous `exit 0 lines 0` — discarded; the rerun below carries a file-count
guard (86 each). Verbatim:

```
ocaml-base-orig exit 0
ocaml-new-c1 exit 0
ocaml-new-c1d exit 0
files: base-orig=86 new-c1=86 new-c1d=86 primary=86
OCAML DIFF base-orig(lem 3c88f0d) vs new-c1d(new lem, C1 sources + 3 fuel_measure declares): exit 0 lines 0
OCAML DIFF new-c1 vs new-c1d (the 3 declares alone): exit 0 lines 0
OCAML DIFF primary generated/ (mtime 2026-09-03 15:12) vs new-c1d: exit 0 lines 0
OCAML DIFF primary generated/ vs base-orig: exit 0 lines 0
LEAN GEN exit 0 files 170 error-lines 1
./gen.sh  120.15s user 1.76s system 99% cpu 2:01.92 total
```

(`error-lines 1` is `lean-gen.log:180: Warning: renaming 'Error' to 'Error0'
for target lean`, matched by the grep; 0 errors.) The primary checkout's
`ocaml_frontend/generated/` is NOT git-tracked (the task brief's
"committed" is imprecise): it is the build tree dated 2026-09-03 15:12
with its `lem_sync.sha256` stamp — and it is byte-identical to both the
`3c88f0d` and the `22aa0fb` output, which pins its provenance as well as a
commit would.

### 2.3 Cerberus Lean generation — the four sites (`.tmp/cerb/lean-gen`)

```
lean-gen/Ctype.lean:442:def ctypeEqual (c : ctype) (c0 : ctype) : Bool := ctypeEqual_lemFuel (ctype.lemSize c) c c0
lean-gen/Ctype.lean:449:    isEqual    :=  ctypeEqual
lean-gen/Core.lean:222:def eq_core_base_type ( bTy1 : core_base_type) ( bTy2 : core_base_type) : Bool := eq_core_base_type_lemFuel (core_base_type.lemSize bTy1)  bTy1  bTy2
lean-gen/Core.lean:228:    isEqual   :=  eq_core_base_type
lean-gen/Defacto_memory_aux.lean:70:def fake_mem_value_eq ( mval1 : impl_mem_value) ( mval2 : impl_mem_value) : Bool := fake_mem_value_eq_lemFuel (impl_mem_value.lemSize mval1)  mval1  mval2
lean-gen/Defacto_memory_aux.lean:77:    isEqual   :=  fake_mem_value_eq
411:inductive monTrace  [LemFuel] : (pre_execution) → (incState) → (incState) → Prop where
```

The Lean tree was NOT built here (per the brief; the record's §4.4 build
is the worker's claim, unverified by this audit).

### 2.4 Adversarial probes — size functions (`.tmp/probes/`, `.tmp/probe-pkg-428`, `.tmp/probe-pkg-432`)

Sources (`open import Pervasives`; each with a fuel'd `List.foldl`
recursion measured by `lemSize`):

| probe | type block(s) | result |
|---|---|---|
| `adv_mutual_nested` | `type a1 = A0 \| A1 of list (maybe (a1 * b1)) and b1 = B1 of maybe (list a1) * nat` | 6 defs in one `mutual`, 4 helpers under `a1.`; `a1.lemSize (A1 [some (A0, B1 (some [A0]) 3), none]) = 9` by `decide`; axiom-free |
| `adv_record_rec` | `type node = <\| nval : nat; kids : list node \|>` (a `structure`); `type flatrec = <\| lemSize : nat; other : bool \|>` | `node.lemSize` over `.mk`; `flatrec.lemSize` stays the projection (no derived size, no collision) |
| `adv_submodule` | `module M = struct type mt = ML \| MN of list mt end`, measured from outside | emitted inside `namespace M` as `mt0.lemSize`; measure resolves to `M.mt0.lemSize m` |
| `adv_opt_list_self` | `type ol = OL of maybe (list ol)`; `type e1 = E of either (e1 * nat) (list e1) \| EN` | option-of-list helper pair; `Sum.inl (x1, _)` tuple pattern; values pinned |
| `adv_param_recpos` | `type rose 'a = Rose of 'a * list (rose 'a)`; `type rr = RL \| RR of rose rr`; `type box 'a = Box of list 'a`; `type tb = TL \| TB of box tb`; `type tc = TCL \| TC of list tc * box tc` | `rose.lemSize {a : Type}`; `rr`/`tb` get NO size (leaf-only); `tc` counts the list, not the box (NOTE-2) |
| `adv_cross_block` | `type u = U of list u \| UL`; `type ul = list u`; `type t = T of ul * list t \| TL`; measure `lemSize x + lemSize y` | the abbreviated other-block field is a leaf; both parameters resolve: `tu_lemFuel (t.lemSize x + u.lemSize y) x y` |
| `adv_ctor_lemSize_nonrec` | `type nr = lemSize of nat \| Other` beside a recursive `tr` | accepted: `nr.lemSize` is the constructor (no derived size for `nr`); `tr.lemSize` unaffected |
| `adv_value_lemSize` | `let lemSize (x : nat) : nat = x + 1` beside `tr` | accepted: the value `lemSize` and `tr.lemSize` coexist; `usev = 4` by `rfl` |
| `adv_nonuniform` | `type nest 'a = NLeaf of 'a \| NNode of nest (list 'a)` | generates; the `inductive` itself fails in Lean (pre-existing, NOTE-5) |
| refusals: `adv_tb_measure`, `adv_fn_field`, `adv_type1`, `adv_param_named_lemSize`, `adv_neg_libtype`, `adv_neg_reptype`, `adv_neg_dotparam` | see MINOR-1/2, NOTE-1; `lemSize p.1` → FM-size-param; `lemSize l` (`l : list nat`) → "not a generated inductive type of this invocation" | all `exit 1` with the FM-size-* tag |

Lean 4.28.0 (`probe-pkg-428`, LemLib from a `.lake`-free copy of this
tree's `lean-lib`, `capped`, 16G; `AdvCheck.lean`/`AdvCheck2.lean`
hand-written — 36 `decide`/`rfl` pins, 8 `#print axioms`), verbatim:

```
warning: Adv_ctor_lemSize_nonrec.lean:49:0: unused `termination_by`, function is not recursive
warning: Adv_ctor_lemSize_nonrec.lean:53:0: unused `termination_by`, function is not recursive
info: AdvCheck.lean:15:0: 9
info: AdvCheck.lean:23:0: 'a1.lemSize' does not depend on any axioms
info: AdvCheck.lean:24:0: 'b1.lemSize' does not depend on any axioms
info: AdvCheck.lean:30:0: 'node.lemSize' does not depend on any axioms
info: AdvCheck.lean:37:0: 'M.mt0.lemSize' does not depend on any axioms
info: AdvCheck.lean:47:0: 'ol.lemSize' does not depend on any axioms
info: AdvCheck.lean:48:0: 'e1.lemSize' does not depend on any axioms
info: AdvCheck.lean:54:0: 'rose.lemSize' does not depend on any axioms
info: AdvCheck.lean:61:0: 2
info: AdvCheck.lean:62:0: lem: fuel exhausted
backtrace:
info: AdvCheck.lean:62:0: 1
info: AdvCheck.lean:73:0: 't.lemSize' does not depend on any axioms
Build completed successfully (47 jobs).
```

(the two warnings are the pre-existing derived-comparison
`termination_by` on the non-recursive `nr` — lines 49/53 are
`nr.beq_derived`/`nr.compare_derived`, not size functions; no size block
warned on either toolchain, confirming the record's "mixed block without
warnings"). Lean 4.32.2 (`probe-pkg-432`: `Adv_mutual_nested`,
`Adv_record_rec`, `Adv_opt_list_self`, the indreln probes and their checks):
`Build completed successfully (40 jobs).`

Two rebuilds of the probe PACKAGE were mine, not the backend's: importing
two probes that both define `spin_lemFuel`/`tr.lemSize` at top level
("environment already contains …") — split into `*Check2.lean`; and two
wrong expected values in my own pins (`node` 6→7, `tu` 3→2), corrected
after `decide` reported them false.

### 2.5 Adversarial probes — fuel-lifted inductive relations

`adv_indreln.lem`: `indreln [ev : nat -> bool] and [od : nat -> bool]`
where only `ev_s`'s premise calls the fuel'd `spin`; a polymorphic
`indreln [preach : forall 'a. 'a -> nat -> nat -> bool]` with a `spin`
premise; `indreln [mreach …]` whose premise calls the MEASURED `mspin`;
`assert mreach_ok : (mreach 0 0)`. Output, verbatim:

```
inductive od  [LemFuel] : (Nat) → Prop where
  | od_s : ∀ n, ( ev  n) → od   (n  +   1)
inductive ev  [LemFuel] : (Nat) → Prop where
  | ev_z : ev    0
  | ev_s : ∀ n, ( od  n) → ((spin  n)  =  (  0)) → ev   (n  +   1)
end
inductive preach (a : Type) [LemFuel] : (a) → (Nat) → (Nat) → Prop where
  | pr_refl : ∀ x n, preach a  x  n  n
  | pr_step : ∀ x n m, ( preach a  x  n  m) → ((spin  m)  =  (  0)) → preach a  x  n  (m  +   1)
inductive mreach  : (Nat) → (Nat) → Prop where
```

— the block lifts together (`od` carries the binder), the type parameter
precedes the instance, the measured-premise relation is fuel-FREE (no
binder; its assert is accepted). `AdvIndrelnCheck.lean` (both toolchains,
green): `example : [LemFuel] → Nat → Prop := @od`, `example : (a : Type) →
[LemFuel] → a → Nat → Nat → Prop := @preach`, `example : Nat → Nat → Prop
:= mreach`, a derivation `@ev ⟨5⟩ 2` whose premise `spin 1 = 0` the kernel
decides at `⟨5⟩` and `¬ (@spin ⟨1⟩ 1 = 0)` by `decide`. Refusals: the
suite's `neg_fuel_indreln_scope` (an assert on a fuel-lifted relation: "OK
(rejected as declared)"); a `lemma` on one is DROPPED, not refused (MINOR-3);
a `def` using one as a `bool` fails in Lean on `Prop`/`Bool` (pre-existing,
NOTE-5).

### 2.6 Non-Lean invariance of the probes (`.tmp/probes/inv.log`, `inv2.log`)

For every probe, `ocaml`/`hol`/`isa`/`coq` with (a) the new lem on the
declared source vs the stripped source (`grep -v '^declare {lean}'`), and
(b) lem `3c88f0d` vs the new lem on the stripped source (the baseline
cannot parse `fuel_measure`, so the declared source is not comparable across
lems). All 15 probes (+ `adv_indreln_use`): 5-8 artifacts each, `base(strip)
-vs-new(strip) diff lines=0`; `declared-vs-stripped diff lines=0` for 14 of
15 — the exception is `adv_indreln` (5 lines), entirely the assert's
source-location string (`line 34` vs `line 31`, NOTE-6):

```
< let _ = run_test "mreach_ok" "File \"adv_indreln.lem\", line 34, character 1 to line 34, character 31\n" (
> let _ = run_test "mreach_ok" "File \"adv_indreln.lem\", line 31, character 1 to line 31, character 31\n" (
```

## 3. Code review notes (read, not just run)

- `lean_size_shape` never produces `CSbad`; the emitter's `CSbad -> assert
  false` is unreachable by construction (fine). `lean_typ_refs_paths` gates
  every field first, so a field that mentions no sibling is a leaf without
  head-normalising — correct and cheap.
- Census and emitter share `lean_size_block` on the same `ts_list`; the
  census is first-registration-wins and idempotent, reset in
  `St.reset_invocation`; `lean_analysis_prepass_all` sets
  `St.current_module_name` per module before the pass, so `is_library_module`
  sees the right name (checked).
- Helpers are memoised per block by the rendered element type and named
  under the FIRST member (`a1.lemSize_aux3` used by `b1.lemSize`); the
  collision check scans every member's constructors/fields for
  `lemSize`/`lemSize_aux*` — over-refuses a `b1` constructor named
  `lemSize_aux1` (harmless, fail-closed).
- `lean_render_measure`: `lemSize` is tested before the parameter check
  (NOTE-1); `mentions` is incremented on a resolved `lemSize x`, so FM-const
  cannot misfire on a pure `lemSize x` measure; the `String.contains x '.'`
  guard sends `lemSize p.1` to FM-size-param (probed).
- Indreln lifting: `Indreln` is registered in `lean_fuel_prepass` with
  defined = the block's relations, used = the premises' constants, so
  lifting is transitive through relations; `fuel_lifted_rel` is inert under
  `rendering_comment`; `St.fuel_binder` is restored with `Fun.protect`. The
  binder is appended after `free_vars_typeset` (probed: `(a : Type)
  [LemFuel]`).
- The OCaml/HOL/Isabelle/Coq emitters are untouched by the diff (only
  `src/lean_backend.ml` changes under `src/`); the net and the invariance
  runs are the measured confirmation.

## 4. Not checked, and why

- The cerberus Lean BUILD of the generated tree (record §4.4, 4:39) —
  excluded by the brief; generation was reproduced and the four sites +
  tallies checked instead.
- The three cerberus obligation proofs (C1's work; do not exist yet).
- Why the target_rep'd type is absent from the census (MINOR-2) — reported
  as measured, cause not traced.
- Lean 4.32.2 on the FULL probe set (only the indreln probes and three
  size blocks were built on 4.32.2; the rest on 4.28.0).
- `p_lem_size` parity beyond the suite's own run (green in §2.1).
- Nothing took over 10 minutes except the suite itself (10:22, a single
  `make lean`, expected ~8-10 min per the record).
