# Fuel-measure slice — record (2026-09-04)

Branch `arc/structural-declare` (lem-lean), continuing from `020df26` (the
structural-declare slice) on mainline `mdd/lean-backend` @ `9ba8970`.
Charter: the FUEL-MEASURE enabler for the cerberus half of the
fuel-parameter arc — the Lean-only mechanism for the PURE case of the
operator's ruling on the (A) census. Worker [AGENT] (lem-lean); the ruling
paraphrased with [USER] provenance; every quoted output is verbatim
from this worktree (`.tmp/` logs named); tallies marked "derived" are
derived. Nothing merged, nothing pushed.

## 0. Commits

| Commit | Content |
|---|---|
| `005f9bb` | lean-lib: regenerate `LemLib/Num.lean` after D4 (comment-only; the D4 commit had not included the regeneration — `make lean-libs` reproduces exactly this diff) |
| `af5d431` | The `fuel_measure` declare: lexer/parser/ast/typed_ast/typecheck/echo/Ott; backend (`lean_fuel_measure_check`, `lean_render_measure`, the measured wrapper, the obligation into the auxiliary file, the fuel fixpoint on ambient constants); tests (positive ×3 modules + 2 proofs modules + `TestFuelMeasureImpl`, kernel pins, 12 negative probes, parity probe + proofs + NEW pin, invariance witness, contextual keywords); gate F3 refinement; `make clean` symlink-only; `.gitignore` negation; parity runner `.proofs.lean`; manual, DESIGN, README, TODO rows 15/16, design note R3 |
| `d8a17e3` | the point-free-tail `_zero` lemma fix (found on the cerberus dry run) + its test/pin; this record; TODO row 17 |

## 1. The ruling this slice implements

[USER 2026-09-04]: keep to the principle that the lem structure is not
changed for OCaml's sake — a good design rule, available here via option
(2); it costs more work, but bounded, kernel-checked work, so take the
harder, trust-surface-preserving option: the lem structure is maintained
and the additional properties come without any trust decrease.

Operationally (the charter): cerberus's `.lem` bodies are NOT restructured
for Lean's structural checker. For every fuel'd function reachable from
`drive`: (B) functions in a monad with an absorbing element keep the fuel
and an absorbing payload; PURE functions get their fuel INSTANTIATED FROM
A DATA MEASURE of the argument (Lean-side only; the OCaml output is
untouched) plus a per-function kernel-checked SUFFICIENCY THEOREM, proved
on the cerberus side; the residue (functions whose termination depends on
environment well-formedness) is enumerated, not promised. The census this
works from: `2026-09-04_structural-declare-record.md` §6.1 (67 rows).

## 2. Design — decisions, with reasons, and the alternatives

### 2.1 The declare: ``declare {lean} fuel_measure val f = `<measure>` ``

Name and form in the family's style (`fuel val`, `fuel_consumer val`,
`structural val`); `fuel_measure` is a contextual keyword like the others
(`test_contextual_keywords.lem` uses it as a let-name, parameter, record
field, and beside the declare). The backtick payload is a **computable
Lean expression over the function's own parameters**, written with their
lem names.

**Contract.** The worker `f_lemFuel (lemFuel : Nat) …` is byte-identical
to the ambient form. The WRAPPER binds the parameters and starts the
counter from the measure:

```lean
def f (xs : List T) : R := f_lemFuel (List.length xs + 1) xs
```

— no `[LemFuel]` binder, no ambient fuel; `f xs = f_lemFuel (<measure>)
xs` by `rfl`; the kernel computes through it (`decide`/`rfl` on closed
terms — `TestFuelMeasureCheck` (1)). **Propagation:** the fuel fixpoint
(`lean_fuel_prepass`, `exp_needs_fuel`, `workers_need_fuel`) tests
`lean_fuel_is_ambient` = fuel'd AND NOT measured, so a measured constant is
fuel-free for its callers — its consumers inherit no binder
(`uses_mlen`, `maps_mspin`: `TestFuelMeasureCheck` (3)); it can be an
instance method's implementation and is assertable from lem (the suite's
`#eval` asserts on `mlen`, `mspin`, `mev`, `mtsum`, `mdepth`). A measured
function whose BODY passes the ambient on to another fuel'd function is
fuel-lifted as any def is (it takes `[LemFuel]` for the callee's sake; its
own counter is still the measure — `mouter`, pinned at two fuels; the
prepass and the block's ambient-reach test must agree, checked as an
internal error). Reader lifting composes (the wrapper binds the reader
parameter first — `msum_amb`); a truly mutual fuel'd block is all-or-none
(`mev`/`modd`: one shared counter, each wrapper starting it from its own
measure).

**Fail-closed rules** (`lean_fuel_measure_check` at the pre-pass, run
FIRST so a conflict is reported as such; `lean_render_measure` and the
emission guards), each a negative probe:

| Rule | Refuses | Probe |
|---|---|---|
| FM-nofuel | a measure without the fuel declare (the worker must exist) | `neg_fuel_measure_nofuel` |
| FM-consumer | with `fuel_consumer` (a hand-written implementation reads the ambient; a measure instantiates a GENERATED worker) | `neg_fuel_measure_consumer` |
| FM-structural | with `structural` (no counter to instantiate) | `neg_fuel_measure_structural` |
| FM-free | an unqualified identifier that is not a parameter (`xs` when the parameter is `l`; `length l`) | `neg_fuel_measure_freevar`, `neg_fuel_measure_unqualified` |
| FM-sizeOf | `sizeOf`/`SizeOf` as ANY dotted component — noncomputable (§2.3) | `neg_fuel_measure_sizeof`, `neg_fuel_measure_dotted_sizeof` |
| FM-ambient | `LemFuel` as ANY dotted component (not a data measure) | `neg_fuel_measure_ambient`, `neg_fuel_measure_dotted_ambient` |
| FM-root | a `_root_`-qualified name (audit M1: it bypassed the head-only checks) | `neg_fuel_measure_root_ambient`, `neg_fuel_measure_root_sizeof` |
| FM-literal | a measure that IS a numeral (`` `5` ``) — the deleted magic value | `neg_fuel_measure_literal`; the bare form `= 5` is refused at parse (`neg_fuel_measure_numeric`) |
| FM-const | a measure mentioning no parameter (`Nat.succ Nat.zero`) | `neg_fuel_measure_const` |
| FM-mutual | some but not all members of a truly mutual fuel'd block | `neg_fuel_measure_mutual_partial` |
| FM-supply | on a supply-lifted definition (unsupported combination; TODO row 16) | `neg_fuel_measure_supply` |
| FM-library | in a library module (the library's auxiliary files are not built — the obligation would have no home) | (no probe: the library carries no measure; the check is in the emission path) |
| reserved | the binders `lemFuel`, `_lem…` in a measure; a user parameter named `lemMeasureLe` | reserved-name contract |
| destructuring | a parameter pattern that is not a variable (lem's pattern compiler makes them variables — 65/65 on cerberus, so this is a backstop) | — |

**Why parameters + QUALIFIED names only.** Lean's global namespace is
invisible at generation, so an unqualified non-parameter is
indistinguishable from a free variable; qualification (`List.length xs`,
`Ns.size x`) both resolves the reference and keeps a global from shadowing
a parameter. Dotted projection on a parameter (`xs.length`, `p.2`) is
admitted (the head is the parameter). Parameter tokens are substituted by
the rendered Lean binder (`lean_escape_keyword` — the wrapper's binder uses
the same escaping), so the user writes the lem name. Numerals INSIDE a
measure (`n + 1`) are not magic values — the data measure with an offset,
certified by the obligation; only a numeral AS the measure (or a
parameter-free measure) is refused. The no-numerals gate's F3 was tightened
to match: a numeral is a fuel only as the WHOLE counter argument
(`_lemFuel 5`, `_lemFuel (5)`), so `_lemFuel (1 + List.length l)` is
green — plant-tested (§5.4).

**Alternatives rejected.** (i) A lem-side measure (`val measure …` with a
Lean rep) — changes the OCaml output (a `val` appears there) or needs the
cycle of §2.3 anyway. (ii) Marking parameters in the measure text (`%x`)
— out of the family's style; the qualified-global rule achieves the same
without new syntax. (iii) Accepting `sizeOf` — measured noncomputable
(§2.3).

### 2.2 The sufficiency obligation — STABILITY AT THE MEASURE, stated in the auxiliary file, proved in a hand-written module the build requires

For every measured `f`, into `<Module>_auxiliary.lean`:

```lean
import <Module>_lemMeasureProofs
…
theorem f_measure_sufficient (xs : List T) (lemFuel : Nat) (lemMeasureLe : (List.length xs + 1) ≤ lemFuel) :
    f_lemFuel lemFuel xs = f xs :=
  <Module>_lemMeasureProofs.f_measure_sufficient xs lemFuel lemMeasureLe
```

with `[LemFuel]`/`[Inhabited]`/class-constraint/reader binders mirrored
from the wrapper (the same `binder_of` renders wrapper, `_zero` lemma and
obligation, so the three agree by construction). The statement is
fuel-STABILITY above the measure: at every fuel at or above it the worker
equals the wrapper — the wrapper's value is the fuel-independent value of
the recursion, which is the consumer's per-function fuel-irrelevance
lemma directly (`∀ n ≥ μ x, f_lemFuel n x = f x`, and `f x = f_lemFuel (μ
x) x` by `rfl`). It is NOT "the exhaustion arm is unreachable at μ" (audit
N2: a divergent `f x = f x` with a value sentinel makes it provable for
any measure) — the operational gap below.

**Why the auxiliary file.** It is lem's own home for prover-side
obligations (the HOL/Isabelle/Coq backends put the lemmas the user must
prove in the `Auxiliary` file), and it is already a build root in every
package of this repo and in cerberus's `lakefile.toml` (every module's
`_auxiliary` is listed). So the gate "no measured function ships without
its theorem" is the Lean build itself: the auxiliary file imports the
hand-written proofs module and applies its constant at the exact stated
type — a missing module, a missing theorem, or a theorem of another type
fails the build — but a `sorry`'d (or axiom-backed) theorem of the right
type BUILDS (audit M2, plant P3 green): that case is the suite's token
gate `check_no_sorry_proofs.sh` (phase `lean-no-sorry-proofs`, §10) and,
downstream, cerberus's sorry/axiom gates over its seams. Plant-tested,
verbatim (the `mlen` proof deleted from
`Test_fuel_measure_lemMeasureProofs.lean`):

```
✖ [34/35] Building Test_fuel_measure_lemMeasureProofs (317ms)
error: Test_fuel_measure_lemMeasureProofs.lean:195:14: Unknown constant `Test_fuel_measure_lemMeasureProofs.mlen_measure_sufficient`
error: Lean exited with code 1
error: build failed
```
(restored: `Build completed successfully (35 jobs).`). The proofs module
cannot be imported by the GENERATED module (it needs `f_lemFuel`: a
cycle), which is why the obligation lives in the auxiliary file and not
beside the wrapper. The parity runner installs `probes/<name>.proofs.lean`
as `<Mod>_lemMeasureProofs.lean` and roots it, so a parity probe with a
measured function carries its proofs too (`p_fuel_measure`).

**Why stability and not the completion predicate.** The brief anticipated
a completion predicate `f_completes n x` (the monotonicity exemplar's
shape) with `f_completes (μ x) x` as the statement. Assessed: (a) the
predicate's GENERATION is the Bool-writer instrumentation of every worker
body that the structural-declare record §5 sized L and that refuses the
HOF/lambda self-uses cerberus's bodies have (`List.foldl (fun acc t' =>
… mtsum t')` — the very shape this slice exists for); (b) with the
standing `never_extract fuelExhaustedWith` payload, "`≠ sentinel`" is not
statable (the payload is a witness value), so a completion notion cannot
be black-box; (c) EVERY black-box statement has the same residual gap:
the sentinel is a value in the logic, so an exhaustion whose payload
coincides with (or is masked into) the true value is invisible to the
kernel — stability, sentinel-irrelevance (a worker abstracted over the
sentinel; also considered and rejected: it changes the worker's shape and
still admits `f a == f b` masking) and the fixpoint equation `f x = B[f]
x` all share it; only the syntactic predicate closes it, and it is not
generatable. So the generated obligation is the value-level truth the
consumer's theorems need — stability — and the completion predicate stays
the consumer-side proof TECHNIQUE (completion + monotonicity ⇒ stability;
`TestFuelMonoExemplar.lean`). The residual gap is operational: the loud
`fuelExhausted` convention and the differential lanes see a runtime
exhaustion; the record says so in the manual.

**The proof template** (the cerberus half's per-function obligation):
stability by induction on the data generalizing the two fuels — `∀ f g, μ
x ≤ f → μ x ≤ g → W f x = W g x`; at every recursive call the argument's
measure is strictly smaller, so the hypothesis applies at the decremented
counters; the obligation is the instance `g := μ x`
(`Test_fuel_measure_lemMeasureProofs.lean`: `mlen`, `mspin` (nat by
subtraction), `mrev_acc` (accumulator), `mouter` (`[LemFuel]`),
`msum_amb` (reader), `mev`/`modd` (joint induction for the mutual block)).
For a NESTED inductive, or a body recursing through `List.foldl`, strong
induction on the measure avoids any nested-inductive induction principle:
`child_lt` (a child's size is below its parent's) and `foldl_congr` (a
fold is congruent in the per-child function) —
`Test_fuel_measure_tree_lemMeasureProofs.lean`. Kernel-only tactics, no
option bump; axioms verbatim from the build:

```
info: Test_fuel_measure_lemMeasureProofs.lean:199:0: 'Test_fuel_measure_lemMeasureProofs.mlen_measure_sufficient' depends on axioms: [propext, Quot.sound]
info: Test_fuel_measure_lemMeasureProofs.lean:200:0: 'Test_fuel_measure_lemMeasureProofs.mspin_measure_sufficient' depends on axioms: [propext, Quot.sound]
info: Test_fuel_measure_lemMeasureProofs.lean:201:0: 'Test_fuel_measure_lemMeasureProofs.mev_measure_sufficient' depends on axioms: [propext, Quot.sound]
info: Test_fuel_measure_tree_lemMeasureProofs.lean:114:0: 'Test_fuel_measure_tree_lemMeasureProofs.mtsum_measure_sufficient' depends on axioms: [propext, Quot.sound]
info: Test_fuel_measure_tree_lemMeasureProofs.lean:115:0: 'Test_fuel_measure_tree_lemMeasureProofs.mdepth_measure_sufficient' depends on axioms: [propext, Quot.sound]
```

### 2.3 FINDING: Lean's automatic `SizeOf` is noncomputable — and the same-module cycle

The first build of the suite with `sizeOf l` as the measure, verbatim
(`lake build`, Lean 4.28.0):

```
error: Test_fuel_measure.lean:32:4: failed to compile definition, compiler IR check failed at `mlen`. Error: depends on declaration 'List._sizeOf_inst', which has no executable code; consider marking definition as 'noncomputable'
```

`sizeOf` reduces in the kernel but has no executable code, and a measured
wrapper must EXECUTE (the differential lanes run it). Consequences:

1. Measures are `List.length xs + 1`, `n + 1`, `Int.toNat (max - i) + 1`,
   dotted projections, or a HAND-WRITTEN computable structural size
   function in a Lean module the generated module imports via `declare
   {lean} extra_import` (`TestFuelMeasureImpl.treeSize` in the suite;
   `CerbMeasureMem`/`CerbMeasureCore` in the dry run, §6). `sizeOf` is
   refused with that reason (FM-sizeOf).
2. A size function over a type defined in the SAME module as the measured
   function cannot be hand-written: that module would have to import the
   generated one — a cycle. Cerberus has exactly two such functions:
   `ctypeEqual` (`ctype.lem`, over `ctype`) and `eq_core_base_type`
   (`core.lem`, over `core_base_type`) — the two D2 equalities that are
   also instance methods. They need a BACKEND-DERIVED size (`t_lemSize`,
   the derived-comparison machinery's shape; TODO row 15) or, until then,
   the (A) sibling rewrite the structural-declare record demonstrated
   (used in the dry-run copy). Decision for the operator (§8).
3. A hand-written size function is itself a total structural def (Lean
   4.32.2 accepted every one in §6 — mutual structural recursion over the
   nested inductives through `List (identifier × ctype × impl_mem_value)`
   and friends), so the kernel computes through the measure and the
   obligation's proof has its equation lemmas.

### 2.4 A second finding, fixed here: the `_zero` lemma of a point-free tail

Compiling the cerberus tree for the first time with `[LemFuel]` (the
fuel-parameter arc's output had been generated, never built) surfaced, in
`Nondeterminism.lean` (identical in the trees with and without measures —
pre-existing), verbatim:

```
error: generated/Nondeterminism.lean:324:4: don't know how to synthesize implicit argument `α`
error: generated/Nondeterminism.lean:324:64: don't know how to synthesize implicit argument `cs`
```

at `theorem liftAction_lemFuel_zero … : liftAction_lemFuel 0 get2 put1
liftInfo liftErr = (fun _ => NDkilled …) := rfl`: `liftAction`'s head
binds four parameters while its type has five arrows (a point-free
`function` tail), so at counter 0 the worker IS a function and the
sentinel lambda's implicit type arguments have nothing to unify with. Fix
(`src/lean_backend.ml`, this record's commit): when the head binds fewer
parameters than the type has arrows (and not under supply lifting), the
lemma's left-hand side is ascribed the codomain —
`(liftAction_lemFuel 0 get2 put1 liftInfo liftErr : nd_action a info1 err1
cs st1 → nd_action a info2 err2 cs st2) = …` — after which
`Nondeterminism` built (§6.3). Test: `tail_spin` in `test_fuel_param.lem`
(`val tail_spin : forall 'a. nat -> 'a -> 'a`, sentinel `` `fun x => x`
``), generated verbatim:

```lean
theorem tail_spin_lemFuel_zero  {a : Type} ( n : Nat) :
    (tail_spin_lemFuel 0  n : a → a) = (fun x => x) := rfl
```

pinned in `TestFuelParamCheck.lean` (`(tail_spin_lemFuel 0 n : Nat → Nat)
= (fun x => x)`; `@tail_spin Nat ⟨3⟩ 2 7 = 7 := by decide`). No other
generated text changes (the 65 cerberus `_zero` lemmas without a tail are
unchanged).

### 2.5 Plumbing

Mirrors `fuel`: lexer (`fuel_measure` → `FuelMeasure`, contextual), parser
(`Declare targets_opt FuelMeasure Val id Eq BacktickString` →
`Decl_fuel_measure_decl`; the `Eq Num` form refused with its reason, as
the fuel budget is), `ast.ml`, `typed_ast.ml(i)` `Decl_fuel_measure` and
`const_descr.fuel_measure : string Targetmap.t`, `typecheck.ml`,
`convert_relations.ml`, the human-target echo in `backend.ml`, the Ott row
`fuel_measure_decl`. ocamlyacc at the final grammar, verbatim: `5 rules
never reduced` / `2 shift/reduce conflicts, 2 reduce/reduce conflicts.` —
unchanged. Backend state: one `[file]` field
(`St.measure_obligations`, reset per file, consed per member and reversed
per block so the auxiliary file lists obligations in declaration order);
`lean_defs` prepends the proofs import to the auxiliary output when the
list is non-empty. The suite: `make clean` now removes only the generated
SYMLINKS in `lean-test/` (a hand-written `Test_<x>_lemMeasureProofs.lean`
must survive it; `.gitignore` gains the matching negation).

## 3. Before / after — one function, verbatim

`tests/comprehensive/test_fuel_measure.lem`, `mlen` and its consumer.
BEFORE (the same source without the `fuel_measure` line, this lem — the
fuel-parameter arc's ambient form):

```lean
def mlen [LemFuel] : List (Nat) → Nat := mlen_lemFuel LemFuel.fuel
theorem mlen_lemFuel_zero ( l : List (Nat)) :
    mlen_lemFuel 0  l = (999) := rfl

def  uses_mlen [LemFuel]  (l : List (Nat))  : Nat :=  mlen  l  +   1
```

AFTER (`Test_fuel_measure.lean` / `Test_fuel_measure_auxiliary.lean`):

```lean
def mlen ( l : List (Nat)) : Nat := mlen_lemFuel (List.length l + 1)  l
theorem mlen_lemFuel_zero ( l : List (Nat)) :
    mlen_lemFuel 0  l = (999) := rfl

def  uses_mlen  (l : List (Nat))  : Nat :=  mlen  l  +   1
```
```lean
import Test_fuel_measure_lemMeasureProofs
…
theorem mlen_measure_sufficient ( l : List (Nat)) (lemFuel : Nat) (lemMeasureLe : (List.length l + 1) ≤ lemFuel) :
    mlen_lemFuel lemFuel  l = mlen  l :=
  Test_fuel_measure_lemMeasureProofs.mlen_measure_sufficient  l lemFuel lemMeasureLe
```

The worker is byte-identical; the wrapper binds `l` and starts the counter
from the measure; the consumer lost its binder; the obligation is a
theorem the build requires. The reader case (`msum_amb`):
`def msum_amb (_lemReader_amb : Nat) ( l : List (Nat)) : Nat :=
msum_amb_lemFuel (List.length l + 1) _lemReader_amb  l`; the
ambient-passing case (`mouter`): `def mouter [LemFuel] ( l : List (Nat))
: Nat := mouter_lemFuel (List.length l + 1)  l`.

## 4. The test theorem (the template), verbatim

```lean
theorem mlen_stable (l : List Nat) (f g : Nat) (hf : List.length l + 1 ≤ f) (hg : List.length l + 1 ≤ g) :
    mlen_lemFuel f l = mlen_lemFuel g l := by
  induction l generalizing f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g => simp [mlen_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f =>
      cases g with
      | zero => omega
      | succ g =>
        simp only [List.length_cons] at hf hg
        simp only [mlen_lemFuel]
        rw [ih f g (by omega) (by omega)]

theorem mlen_measure_sufficient (l : List Nat) (lemFuel : Nat) (lemMeasureLe : List.length l + 1 ≤ lemFuel) :
    mlen_lemFuel lemFuel l = mlen l :=
  mlen_stable l lemFuel (List.length l + 1) lemMeasureLe (Nat.le_refl _)
```

The nested-inductive / `foldl` template (`mtsum` over `mtree` with
`List.foldl (fun acc t' -> acc + mtsum t')` AS WRITTEN in lem): strong
induction on `treeSize t`, `child_lt`, `foldl_congr`
(`Test_fuel_measure_tree_lemMeasureProofs.lean`).

## 5. Gates — verbatim

### 5.1 tests/comprehensive `make lean` on `af5d431` (clean: `make clean` then `make lean`; `.tmp/gate1.log`)

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
  [68 × "OK (rejected as declared)" — derived count; the 12 neg_fuel_measure_* among them]
  OK: inv_fuel.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_fuel_measure.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_reader_consumer.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_structural.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_supply.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
=== p_fuel_measure ===
  REBASELINED pin …/parity/expected/p_fuel_measure.out      (first run only: a NEW probe's pin, recorded from the OCaml reference)
  OK: parity (8 lines byte-identical to the OCaml reference; pin matches)
  [parity: 23 × "OK: parity", 6 × "OK: both fail", 4 × XFAIL (the registered f_int_of_big_num, f_int32_overflow, p_str_bytes, p_str_escapes) — derived counts]
  OK: 236 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make lean  276.04s user 55.94s system 130% cpu 4:14.00 total
EXIT 0
```

The auxiliary files' generated asserts on measured functions, from the
build: `PASS: mlen_ok`, `PASS: mspin_ok`, `PASS: mrev_acc_ok`, `PASS:
mev_ok`, `PASS: maps_mspin_ok`, `PASS: mtsum_ok`, `PASS: mdepth_ok`,
`PASS: ctx_kw_fuel_measure_decl_ok`.

### 5.2 `make lean` on `d8a17e3` (the `_zero` fix)

Clean (`make clean` then `make lean`; `.tmp/gate2.log`), after the
`_zero` fix and the `tail_spin` test/pin:

```
=== Generation: 51 passed, 0 failed, 0 skipped ===
Build completed successfully (151 jobs).
  [68 × "OK (rejected as declared)"; 5 invariance OK incl. inv_fuel_measure.lem; parity 23 OK / 6 both-fail / 4 XFAIL — derived counts, as in 5.1]
  OK: 236 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make lean  297.12s user 35.26s system 121% cpu 4:34.04 total
EXIT 0
```

tests/nonlean-regress on the same tree: `nonlean-regress: OK (893 artifact
rows, 216 exit rows, 9 emitters, byte-identical to golden)`.

### 5.3 lean-lib

`lake build` (capped): `Build completed successfully (37 jobs).`;
`grep -rn "^axiom " lean-lib/ --include='*.lean'`: 0 hits. The only
lean-lib change is the D4 regeneration of `LemLib/Num.lean` (comment-only,
`005f9bb`).

### 5.4 The no-numerals gate, refined and plant-tested (`.tmp/gate1.log` context; run by hand)

```
=== gate baseline ===
  OK: 236 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
=== plant F3a: mlen_lemFuel 5 l ===
  FAIL (F3): fuel numeral shape found:
…/tests/comprehensive/Test_fuel_measure.lean:32: def mlen ( l : List (Nat)) : Nat := mlen_lemFuel 5 l
exit 1
=== plant F3b: mlen_lemFuel (5) l ===
  FAIL (F3): fuel numeral shape found:
…/tests/comprehensive/Test_fuel_measure.lean:32: def mlen ( l : List (Nat)) : Nat := mlen_lemFuel (5) l
exit 1
=== plant F3c (must stay green): mlen_lemFuel (1 + List.length l) l ===
  OK: 236 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
exit 0
```

### 5.5 tests/nonlean-regress

`nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters,
byte-identical to golden)` — NO rebaseline: the net's corpus
(`library/*.lem`, `tests/backends/*.lem`) contains no source using the new
declare, and the grammar addition changes no non-Lean output.

### 5.6 OCaml byte-identity of the cerberus tree (`.tmp/cerb`)

`frontend/` of cerberus-lean primary @ `1b57bcf26` copied, the five
numeric fuel lines deleted (both lems refuse them), `LEM_SRC` = 86 files
and the Makefile's flags obtained with `make --eval`, `LEMLIB` = this
tree's library; baseline lem = `9ba8970` rebuilt from `git archive`
(`.tmp/lem-base`, `make build-lem`); verbatim:

```
base exit 0
new exit 0
files: base=86 new=86
OCAML DIFF exit 0 lines 0
```

The copy WITH the 38 `fuel_measure` declares cannot be parsed by the
baseline lem (exit 1 — as for every new `{lean}` declare); this lem on
that copy vs this lem on the same copy with the declares stripped differs
only in the generated-header source path (`frontend-strip/…`), one blank
line per inserted `extra_import` line, and the scratch `(* DRY-RUN COPY
*)` comments re-attached by the known declare-swallows-comment quirk
(fuel-parameter record §6.2) — no code token (§6.5 checks it with
comments and blank lines stripped).

## 6. The cerberus dry run (read-only; `.tmp/cerb`, scratch copy of `frontend/` @ `1b57bcf26`)

### 6.1 Method

1. Census input: the 67-row table (structural-declare record §6.1) plus a
   per-function extraction (val type, parameters after lem's pattern
   compilation — read from the generated `_zero` lemmas —, codomain kind,
   every recursive call's arguments, the recursion driver) — the
   classification below is [AGENT], each row's driver is a claim checked
   by the compile column where a measure was tried.
2. Copy patches, all in `.tmp/cerb` only: the five numeric fuel lines
   deleted; the D2 sibling rewrites of `ctypeEqual`/`ctypeParamsEqual`
   and `eq_core_base_type`/`eq_core_base_types` as `structural` (same
   module as their type — §2.3 item 2); the `monStep` indreln rule
   removed (its premise references the fuel-lifted `monStep`;
   fuel-parameter record §6.3); 38 `declare {lean} fuel_measure val` lines
   + `extra_import` of two scratch seams `CerbMeasureMem.lean`
   (`ctypeSize`, the defacto memory value block: `ivalSize`, `mvSize`,
   …) and `CerbMeasureCore.lean` (`patternSize`, `pexprSize`, `exprSize`
   — counting expr nodes only, so a substitution into an expr's pexprs
   preserves it —, `memValueSize` over `CerbMem.MemValue`), all
   `termination_by structural`.
3. Generation: this lem, cerberus's flags, `LEM_SRC_LEAN` (85 files):
   `lean gen exit 0`, 170 files. Derived counts, tree without vs with
   the 38 measures: `[LemFuel]` binders 391 → 284; ambient wrappers
   (`_lemFuel LemFuel.fuel`) 64 → 27; measured wrappers 0 → 38; generated
   obligations 38 in 7 auxiliary files (`Core_aux`, `Core_run_aux`,
   `Core_reduction`, `Core_eval`, `Defacto_memory`, `Defacto_memory_aux`,
   `Utils`).
4. Build: cerberus's `lean_frontend` (seams per the hand-written
   manifest, `lakefile.toml` with LemLib re-pointed to a scratch COPY of
   this tree's `lean-lib` — a `path` dependency shares its `.lake` with
   whoever builds it; the suite's Lean 4.28.0 and cerberus's 4.32.2 would
   otherwise trash each other's oleans, measured: `incompatible header`),
   Lean 4.32.2, `CERB_MEM_MAX=16G`, the `_auxiliary` roots dropped (their
   obligations need proofs modules that the dry run does not write — no
   `sorry` anywhere, including scratch) and the two measure seams added.
   Two scratch STOPGAPS in the copy's `CerbMem.lean`, neither the design:
   `def lemDefaultFuel : Nat := 100000000` (its 14 hand-written
   `_lemFuel lemDefaultFuel` entries) and `instance : LemFuel :=
   ⟨lemDefaultFuel⟩` (its 12 `nd_bind` call sites — F2, the very hazard
   the gate forbids), so that the build reaches the measured modules;
   both are rows of the seam work list (§6.4).

### 6.2 The table (67 rows: class, proposed measure, compile verdict)

Classes: **MEASURED** (a data measure proposed and declared in the copy);
**(B)** (monadic, stays ambient; the payload must be the monad's absorbing
element — the cerberus half's check); **RESIDUE** (no data measure — the
reason). Compile: whether the module carrying the measured wrapper built
in §6.3 (`✓`), was not reached (`—`), or the row is not measured (`·`).

| # | function (file) | class | measure (Lean, over the worker's parameters) / reason | compile |
|---|---|---|---|---|
| 1 | `showNonNegativeWithBasis_aux` (formatted) | RESIDUE | recursion on `n / b`: terminates only for `b ≥ 2` (for `b ≤ 1` the OCaml loops) — a precondition, not a data measure | · |
| 2 | `load_character_array_aux` (formatted) | (B) | `memM` = ND; memory walk (pointer shifted per step, stops on NUL/`Just 0`) | · |
| 3 | `many` (monadic_parsing) | RESIDUE/(B) | `parserM` (list-of-parses monad; failure = `[]`); terminates only if `p` consumes input — not a measure of `p` | · |
| 4 | `many1` (monadic_parsing) | RESIDUE/(B) | sibling of `many` | · |
| 5 | `add_to_sb` (core_run_aux) | MEASURED | `CerbMeasureCore.exprSize g` | ✓ |
| 6 | `add_to_asw` (core_run_aux) | MEASURED | `CerbMeasureCore.exprSize g` | ✓ |
| 7 | `convert_pexpr` (core_run_aux) | MEASURED | `CerbMeasureCore.pexprSize g` | ✓ |
| 8 | `convert_expr` (core_run_aux) | MEASURED | `CerbMeasureCore.exprSize g` (its wrapper keeps `[LemFuel]`: the body passes the ambient on) | ✓ |
| 9 | `ctypeEqual` (ctype) | SAME-MODULE (TODO 15) | the size over `ctype` would have to live in `Ctype.lean` — a backend-derived size; dry-run copy: the D2 `structural` sibling rewrite (builds) | ✓ (rewrite) |
| 10 | `zeros_aux` (core_aux) | RESIDUE | tag lookup `Map.lookup tag tagDefs` (Struct/Union member types are not subterms) | · |
| 11 | `in_pattern` (core_aux) | MEASURED | `CerbMeasureCore.patternSize g` | ✓ |
| 12 | `subst_wait` (core_aux) | MEASURED | `CerbMeasureCore.exprSize g` | ✓ |
| 13 | `find_labeled_continuation2_aux` (core_aux) | MEASURED | `CerbMeasureCore.exprSize g` | ✓ |
| 14 | `loadedValueFromMemValue` (core_aux) | MEASURED | `CerbMeasureCore.memValueSize mem_val` (over the seam's `CerbMem.MemValue`) | ✓ |
| 15 | `memValueFromValue` (core_aux) | MEASURED | `CerbMeasureMem.ctypeSize ty1` (recursion through `unatomic ty1`: the proof needs `ctypeSize (unatomic t) ≤ ctypeSize t`); wrapper keeps `[LemFuel]` | ✓ |
| 16 | `subst_sym_pexpr` (core_aux) | MEASURED | `CerbMeasureCore.pexprSize g` | ✓ |
| 17 | `subst_sym_expr` (core_aux) | MEASURED | `CerbMeasureCore.exprSize g` | ✓ |
| 18 | `subst_pattern_val` (core_aux) | MEASURED | `CerbMeasureCore.patternSize g` (the expr is an accumulator: only the pattern decreases) | ✓ |
| 19 | `unsafe_subst_sym_pexpr` (core_aux) | MEASURED | `CerbMeasureCore.pexprSize g0` (the third parameter) | ✓ |
| 20 | `unsafe_subst_sym_expr` (core_aux) | MEASURED | `CerbMeasureCore.exprSize g` | ✓ |
| 21 | `unsafe_subst_pattern` (core_aux) | MEASURED | `CerbMeasureCore.patternSize g` | ✓ |
| 22 | `subst_pattern` (core_aux) | MEASURED | `CerbMeasureCore.patternSize g` | ✓ |
| 23 | `match_pattern` (core_aux) | MEASURED | `CerbMeasureCore.patternSize g` | ✓ |
| 24 | `to_pure` (core_aux) | MEASURED | `CerbMeasureCore.exprSize g`; the local `to_pure_aux` recurses on `subst_pattern pat pe1 e2` — the proof needs `exprSize (subst_pattern …) = exprSize e2` (substitution into pexprs preserves the expr-node count by construction of `exprSize`) | ✓ |
| 25 | `to_pures` (core_aux) | MEASURED | `CerbMeasureCore.exprsSize l + 1` (sibling, shared counter) | ✓ |
| 26 | `collect_saves_aux` (core_aux) | MEASURED | `CerbMeasureCore.exprSize g` | ✓ |
| 27 | `m_collect_saves_aux` (core_aux) | MEASURED | `CerbMeasureCore.exprSize g` | ✓ |
| 28 | `find_labeled_continuation` (core_aux) | MEASURED | `CerbMeasureCore.exprSize g` | ✓ |
| 29 | `update_env_aux` (core_aux) | MEASURED | `CerbMeasureCore.patternSize g` | ✓ |
| 30 | `are_compatible_aux` (ctype_aux) | RESIDUE | tag lookups in the `tagDefs1`/`tagDefs2` environment (Struct/Union members) | · |
| 31 | `are_compatible_params_aux` (ctype_aux) | RESIDUE | sibling; also a point-free `function` tail (the recursion lists are not named parameters) | · |
| 32 | `are_compatible_params` (ctype_aux) | RESIDUE | sibling | · |
| 33 | `mkListN_aux` (utils) | MEASURED | `Int.toNat (n - i) + 1` (counter `i+1` up to `n`) | ✓ |
| 34 | `mkListFromTo_aux` (utils) | MEASURED | `Int.toNat (max2 - i) + 1` | ✓ |
| 35 | `replicate_list_` (utils) | MEASURED | `n + 1` | ✓ |
| 36 | `list_unfoldr_aux` (utils) | RESIDUE | unfold driven by the client function `ctor` (no decrease on the parameters) — genuinely partial, pure | · |
| 37 | `one_step_unseq_aux` (core_reduction) | RESIDUE (point-free tail) | structural on a list that is the anonymous `function` argument, not a named parameter — a measure cannot name it (one-line eta-expansion in lem would make it MEASURED: `List.length xs + 1`) | · |
| 38 | `has_ccall` (core_reduction) | MEASURED | `CerbMeasureCore.exprSize g` | ✓ |
| 39 | `get_ctx` (core_reduction) | RESIDUE (point-free tail, via sibling) | `exprSize g` would do, but the sibling `get_ctx_unseq_aux` recurses on an anonymous `function` list — all-or-none blocks the pair | · |
| 40 | `get_ctx_unseq_aux` (core_reduction) | RESIDUE (point-free tail) | as 37 | · |
| 41 | `full_eval_pexpr` (core_reduction) | (B) | step-until-value loop on a rewritten pexpr in the SEU monad (exception = absorbing) | · |
| 42 | `print_eval_conv_aux` (driver) | (B) | ND (`memM`), branches of an evaluation result | · |
| 43 | `drive_nonmemory_steps_aux2` (driver) | (B) | ND driver worklist (may grow) | · |
| 44 | `driver2` (driver) | (B) | ND driver loop through the `process_core_step2` continuation | · |
| 45 | `hack` (driver) | RESIDUE | PURE step-until-value loop on a rewritten pexpr (`Core.value` result) — an evaluation loop, not data-bounded | · |
| 46 | `pull_constrained` (core_eval) | MEASURED | `CerbMeasureCore.pexprSize g` (the counter `n+1` increases; the pexpr decreases through the `self` closure) | ✓ |
| 47 | `step_eval_pexpr` (core_eval) | MEASURED | `CerbMeasureCore.pexprSize pexpr1` — the extraction found every `self` argument a component of the matched pexpr (the substitution results go through `EU.return`, not `self`) [AGENT reading; the obligation's proof is the test]; EU monad; wrapper keeps `[LemFuel]` | ✓ |
| 48 | `eval_pexpr_aux2` (core_eval) | (B) | step-until-value loop (EU monad; exception absorbing) | · |
| 49 | `eval_pexpr_aux_broken` (core_eval) | (B) | as 48 | · |
| 50 | `tmp_compl_aux` (defacto_memory_aux) | MEASURED | `nbits + 1` | ✓ |
| 51 | `tmp_AND_aux` (defacto_memory_aux) | MEASURED | `nbits + 1` | ✓ |
| 52 | `tmp_OR_aux` (defacto_memory_aux) | MEASURED | `nbits + 1` | ✓ |
| 53 | `tmp_XOR_aux` (defacto_memory_aux) | MEASURED | `nbits + 1` | ✓ |
| 54 | `fake_mem_value_eq` (defacto_memory_aux) | MEASURED | `CerbMeasureMem.mvSize mval1` (`impl_mem_value` lives in `defacto_memory_types` — cross-module; resolves this D2 instance without a rewrite) | ✓ |
| 55 | `simplify_integer_value_base` (defacto_memory_aux) | RESIDUE | rebuilt terms (`IVop IntMul [IVsizeof elem_ty; …]`) AND tag lookup `Ctype_aux.get_structDef` for struct sizeof; the consumer's flagged silent-value payload | · |
| 56 | `nd_bind` (nondeterminism) | (B) | the ND monad's bind (`NDkilled` absorbing) | · |
| 57 | `liftND` (nondeterminism) | (B) | ND, through the stored-function application | · |
| 58 | `liftAction` (nondeterminism) | (B) | sibling; point-free tail — its `_zero` lemma needed the codomain ascription (§2.4) | · |
| 59 | `has_concurRead` (defacto_memory) | MEASURED | `CerbMeasureMem.ivalSize ival_` | ✓ |
| 60 | `find_array_index` (defacto_memory) | MEASURED | `size - i + 1` (ND monad, but data-bounded: counter `i+1` up to `size`) | ✓ |
| 61 | `easy_update_mem_value_aux` (defacto_memory) | MEASURED | `List.length sh + 1` (structural on the shift path in every call; the `is_strong` fallback's tag lookup builds a VALUE, not the recursion argument); wrapper keeps `[LemFuel]` | ✓ |
| 62 | `memcmp_load_aux` (defacto_memory) | MEASURED | `Int.toNat (max_offset - offset) + 1`; wrapper keeps `[LemFuel]` | ✓ |
| 63 | `mkUnspec` (defacto_memory) | RESIDUE | tag lookups `Ctype_aux.get_structDef`/`get_unionDef` | · |
| 64 | `are_compatible` (ail/ailTypesAux) | RESIDUE (point-free tail, via sibling) | structural on both ctypes (tags compared only) — measurable by itself (`ctypeSize p.2 + ctypeSize p0.2`), but the sibling `are_compatible_params_aux` has its lists in an anonymous `function` tail; front-end typing, off the execution path | · |
| 65 | `are_compatible_params_aux` (ail/ailTypesAux) | RESIDUE (point-free tail) | as 37 | · |
| 66 | `are_compatible_params` (ail/ailTypesAux) | RESIDUE | sibling | · |
| 67 | `eq_core_base_type` (core) | SAME-MODULE (TODO 15) | as 9; dry-run copy: the D2 `structural` sibling rewrite (builds) | ✓ (rewrite) |

**Tally (derived from the table's class column; CORRECTED per pre-merge
audit M3 — the first version of this paragraph said 38/11/16/2, with the
sub-labels "tag lookup 5" and "point-free tail 7", which did not match the
table or the names listed; the commit message of `d8a17e3` carries the
wrong numbers and stays as history):** MEASURED 38 (of which 5 keep
`[LemFuel]` because their bodies pass the ambient on: `convert_expr`,
`memValueFromValue`, `step_eval_pexpr`, `easy_update_mem_value_aux`,
`memcmp_load_aux`); (B) 10 (`load_character_array_aux`,
`full_eval_pexpr`, `print_eval_conv_aux`, `drive_nonmemory_steps_aux2`,
`driver2`, `eval_pexpr_aux2`, `eval_pexpr_aux_broken`, `nd_bind`,
`liftND`, `liftAction`); RESIDUE 17 — tag lookup 6 (`zeros_aux`,
`are_compatible_aux` + 2 siblings, `mkUnspec`, and
`simplify_integer_value_base` which is also rebuilt-term), point-free
`function` tail 6 (`one_step_unseq_aux`, `get_ctx` + `get_ctx_unseq_aux`,
`are_compatible` + 2 siblings — a one-line eta-expansion each would make
most MEASURED; decision for the operator, §8), evaluation loop 1
(`hack`), client function 1 (`list_unfoldr_aux`), precondition 1
(`showNonNegativeWithBasis_aux`), parser 2 (`many`, `many1` — the table's
"RESIDUE/(B)" rows, counted here as residue); SAME-MODULE 2
(`ctypeEqual`, `eq_core_base_type`; TODO row 15). 38 + 10 + 17 + 2 = 67.

### 6.3 The build — verbatim

Three rounds, Lean 4.32.2, `CERB_MEM_MAX=16G`, the scratch tree of §6.1 (4).

Round 1 (`.tmp/cerb/build-1.log`, the tree BEFORE the `_zero` fix): 74/142
built, then `✖ [74/142] Building Nondeterminism (475ms)` with the
`liftAction_lemFuel_zero` errors quoted in §2.4 — pre-existing (the
module is byte-identical with and without measures), fixed in the backend
(this record's commit).

Round 2 (`.tmp/cerb/build-3.log`, fixed lem, no seam stopgap for the
ambient sites): 90 modules built — among them `✔ [58/142] Built Utils
(460ms)`, `⚠ [66/142] Built Ctype (656ms)` (the D2 rewrite), `⚠ [75/142]
Built Nondeterminism (541ms)` (the fixed lemma), `Defacto_memory_aux`,
`CerbMeasureMem` — then the seam, verbatim:

```
✖ [95/142] Building CerbMem (3.3s)
error: generated/CerbMem.lean:2072:2: failed to synthesize instance of type class
  LemFuel
[… 12 such errors: the `nd_bind` sites of §6.4 item 1 …]
Some required targets logged failures:
error: build failed
/home/dev/projects/cerberus-lean-proj/cerberus-lean/scripts/capped lake build  159.28s user 11.47s system 140% cpu 2:01.28 total
```

Round 3 (`.tmp/cerb/build-4.log`, the scratch `instance : LemFuel` in the
copy's `CerbMem.lean` standing in for those 12 sites): EVERY module built
— the whole generated tree with the 38 measured wrappers and the two size
seams, verbatim (the ⚠ are the pre-existing derived-comparison
`unused termination_by`/deprecation warnings; 824 warning lines, 0
`error:`):

```
✔ [58/142] Built Utils (460ms)
⚠ [66/142] Built Ctype (656ms)
⚠ [75/142] Built Nondeterminism (541ms)
⚠ [107/142] Built Core (2.0s)
✔ [112/142] Built CerbMeasureCore (376ms)
⚠ [118/142] Built Defacto_memory (2.1s)
✔ [119/142] Built CerbMeasureMem (665ms)
⚠ [120/142] Built Core_aux (2.2s)
⚠ [127/142] Built Core_run_aux (1.2s)
⚠ [129/142] Built Core_eval (1.6s)
⚠ [134/142] Built Core_reduction (1.8s)
⚠ [137/142] Built Defacto_memory_aux (1.1s)
Build completed successfully (142 jobs).
/home/dev/projects/cerberus-lean-proj/cerberus-lean/scripts/capped lake build  77.73s user 5.54s system 282% cpu 29.456 total
EXIT 0
```

So: all 38 measured wrappers COMPILE (their measures typecheck and are
computable; Lean 4.32.2 accepts every hand-written structural size), the
two D2 rewrites build, and the (B)/residue rows compile in their ambient
form as before. What this build does NOT check: the 38 obligations
(auxiliary roots dropped — no proofs, no `sorry`) and the runtime
(differential lanes) — the cerberus half's.

### 6.4 The seam work list (the cerberus half; measured in the copy)

1. `lean_frontend/CerbMem.lean`, the 12 `nd_bind` call sites that failed
   `failed to synthesize instance of type class LemFuel` (Lean 4.32.2,
   `.tmp/cerb/build-3.log`, lines of the copy): `:2072` and `:2109`
   (`allocateObject`, `allocateRegion` — `nd_bind (allocator …)`), `:2435`
   (`nePtrval`), `:2679`/`:2681` (`memcpyM` — `loadM`/`storeM`), `:2714`,
   `:2722`, `:2723` (`memcmpM`), `:2771`–`:2773` (`reallocM`), `:2924`
   (`copyAllocId`). `nd_bind` is (B) — ambient — so each enclosing entry
   takes `[LemFuel]`, and the `mem.lem` consumers whose implementations
   reach them add `declare {lean} fuel_consumer` (fuel-parameter record
   §6.6). The dry run's scratch `instance : LemFuel` stands in for exactly
   these.
2. `CerbMem.lean`'s 14 hand-written `X_lemFuel lemDefaultFuel …` entries
   (`:510` `memberAlign`, `:516` `offsetsofMembers`, `:521` `offsetsof`,
   `:525` `sizeofCtype`, `:529` `alignofCtype`, `:747` `memValueToBytes`,
   `:910`–`:911`, `:1085` `reconstructValue`, `:1227`–`:1228`, `:1255`
   `typeofMval`, `:1287` `unqualifyAndUnatomic`, at cerberus `HEAD`): each
   is a HAND-WRITTEN fuel worker and gets the design's shape by hand —
   measured where the recursion is on the data (`typeofMval`: a
   `MemValue` size; `unqualifyAndUnatomic`: `ctypeSize`; `memValueToBytes`:
   a `MemValue` size; `reconstructValue`: `ctypeSize` if its recursion is
   on the type — to be read), ambient `[LemFuel]` + `LemFuel.fuel` where it
   is a tag lookup (`sizeofCtype`/`alignofCtype`/`offsetsof`/`memberAlign`
   on `Struct`), each with its stability theorem in the seam. The dry run's
   scratch `def lemDefaultFuel` stands in for these.
3. Two seam modules of computable size functions, the dry run's
   `CerbMeasureMem.lean` (`ctypeSize` + the `impl_mem_value` block: 20
   functions) and `CerbMeasureCore.lean` (`patternSize`, `pexprSize`,
   `exprSize`, `memValueSize`: 21 functions), all `termination_by
   structural`, all accepted by Lean 4.32.2 — the cerberus half takes them
   as they are (into `lean_frontend/`, the hand-written manifest and the
   lakefile roots) and adds them to `check_handwritten_sync.sh`. Import
   discipline: `CerbMeasureMem` imports `Ctype` + `Defacto_memory_types`
   (used below `Core`); `CerbMeasureCore` imports `Core` + `CerbMem` (used
   above them).
4. The 38 `declare {lean} fuel_measure val` lines + 2 `extra_import`
   lines of §6.2 in `core_aux.lem` (19), `core_run_aux.lem` (4),
   `core_reduction.lem` (1), `core_eval.lem` (2), `defacto_memory.lem` (4),
   `defacto_memory_aux.lem` (5), `utils.lem` (3) — `{lean}`-scoped; the
   OCaml tree is unchanged (§5.6).
5. 38 obligation proofs in 7 modules `Core_aux_lemMeasureProofs.lean`,
   `Core_run_aux_lemMeasureProofs.lean`, `Core_reduction_…`,
   `Core_eval_…`, `Defacto_memory_…`, `Defacto_memory_aux_…`,
   `Utils_lemMeasureProofs.lean` (hand-written, manifest + roots), each
   theorem stated with exactly the auxiliary file's binders (the generated
   comment above each obligation names the constant). Template §4;
   expected hard rows: 24 (`to_pure`, the size-preservation lemma), 15
   (`memValueFromValue`, `unatomic`), 47 (`step_eval_pexpr`, the largest
   body — `EU.mapM self`).
6. `cmm_op.lem:580` `monStep` rule; `ctype.lem`/`core.lem` D2 equalities:
   the same-module cases await TODO row 15 or the (A) sibling rewrite (the
   dry-run copy uses the rewrite; both build); `fake_mem_value_eq` is
   MEASURED (row 54) — no rewrite needed.
8. (Audit M5, the cerberus half.) A gate that every `generated/*.lean`
   is a root of `lakefile.toml` (fail on drift): today 85 `_auxiliary`
   roots = 85 generated auxiliary files (the auditor's census), but
   nothing checks it, and an auxiliary module dropped from the roots
   silently un-builds its obligations (the auditor's plant P5 on the
   suite's lakefile: green with the obligations unbuilt).
7. `CerbND.lean`: its hand-written `_zero` duplicates and wrapper `rfl`s
   (fuel-parameter record §6.6) — unchanged by this slice; with `liftAction`'s
   `_zero` now carrying the codomain ascription, a hand-written duplicate
   must match that statement or go.

### 6.5 OCaml with vs without the 38 declares (this lem, the copy)

```
strip exit 0
OCAML DIFF (this lem: copy with vs without the 38 fuel_measure declares) exit 1 lines 441; files 86/86
```
Every hunk is the generated-header path (`frontend-strip/` vs
`frontend/`), a blank line where an `extra_import` line was inserted, or
a scratch `(* DRY-RUN COPY *)` comment re-attached to the preceding
definition (the declare-swallows-comment quirk, fuel-parameter record
§6.2); with comments and blank lines stripped from both trees: verbatim
`OCAML DIFF with vs without the 38 declares, comments and blank lines
stripped: exit 1 lines 5 (files 86/86)`, the five lines being ONE hunk of
trailing whitespace (`core_aux.ml:1938` `))` vs `))  ` where the scratch
comment stood) — no code token differs.

## 7. TODO rows

- 15 (new): backend-derived computable size functions for generated
  inductives — the same-module case (`ctypeEqual`, `eq_core_base_type`). M.
- 16 (new): `fuel_measure` on a supply-lifted definition (FM-supply). S.
- 17 (new, this commit): point-free `function` tails — 7 census rows are
  RESIDUE only because the recursion argument is an anonymous `function`
  scrutinee; a one-line eta-expansion in lem (`let rec f acc = function
  …` → `let rec f acc l = match l with …`) names it. Whether that counts
  as "changing the lem structure" is the operator's call (§8). S.
- 13 (note added in `af5d431`): for measured functions the generated
  obligation IS the per-function fuel-irrelevance theorem.

## 8. Decisions for the operator

1. **Same-module measures (TODO 15).** `ctypeEqual` and
   `eq_core_base_type` cannot take a hand-written measure (§2.3). Options:
   (a) fund the backend-derived `t_lemSize` (M; also removes the
   hand-written size seams for every other type); (b) the (A) sibling
   rewrite for these two only (the dry-run copy; semantics-preserving,
   demonstrated in the structural-declare record, but a lem restructuring
   the ruling disfavours); (c) leave them ambient — not possible: they are
   instance methods (D2), so one of (a)/(b) is required for the tree to
   generate.
2. **Point-free tails (TODO 17).** Seven census rows (`one_step_unseq_aux`,
   `get_ctx`/`get_ctx_unseq_aux`, `are_compatible`/`…_params_aux`/
   `…_params` in ail) would be MEASURED after an eta-expansion naming the
   `function` argument — a one-line, semantics-preserving lem edit per
   function that changes the OCaml text trivially (an explicit parameter).
   Is that within the ruling that the lem structure is maintained?
3. **The (B) payloads.** For the 11 (B) rows the cerberus half must make
   each sentinel the monad's absorbing element (`NDkilled …` for ND; an EU
   exception for `eval_pexpr_aux2`/`…_broken`/`full_eval_pexpr`) — the
   consumer's requirement; `many`/`many1` (parser, failure = `[]`) and the
   pure residue (`hack`, `list_unfoldr_aux`, `showNonNegativeWithBasis_aux`)
   have no absorbing element and stay loud-ambient.
4. **The obligation's statement shape** — stability (§2.2) — is [AGENT];
   the consumer may prefer the completion predicate as an ADDITIONAL
   hand-written artefact per function (it implies stability), which the
   design permits without change.

## 9. Not done, and why

- The 38 obligation PROOFS on the cerberus side — the cerberus half's
  work by charter (their statements are generated in the dry run's
  auxiliary files; not typechecked here because no proofs module exists
  and no `sorry` is written, even in scratch).
- Backend-derived size functions (TODO 15).
- `fuel_measure` × supply (TODO 16).
- The Ott derived artifacts (TODO row 5, pre-existing).
- `.tmp/` (baseline lem, the cerberus copies, logs) is ephemeral and
  deleted at slice end; everything load-bearing is quoted above.

## 10. Audit response (pre-merge audit `2026-09-04_structural-measure-audit-premerge.md` @ `e7796a1`, verdict MERGE-WITH-FIXES, no MAJOR)

One commit on `arc/structural-declare` (this section's). Each item, what
changed, and the evidence (verbatim from this worktree, `.tmp/gate3.log`
/ `.tmp/nonlean3.log`).

- **M1 (`_root_` evasion of FM-ambient/FM-sizeOf).** `lean_render_measure`
  now refuses a `_root_` head outright (FM-root) and tests EVERY dotted
  component of every identifier against the forbidden set (`LemFuel`,
  `sizeOf`/`SizeOf`, the reserved `lemFuel`/`_lem…`), before the
  parameter substitution. Four probes; the auditor's two evasions,
  refused at generation, verbatim:
  ```
  Error: Lean backend: the fuel measure of len mentions `_root_.LemFuel.fuel` (FM-root: a `_root_`-qualified name is refused — a qualified global never needs it, and it would bypass the checks on the name's components)
  Error: Lean backend: the fuel measure of len mentions `_root_.sizeOf` (FM-root: a `_root_`-qualified name is refused — a qualified global never needs it, and it would bypass the checks on the name's components)
  Error: Lean backend: the fuel measure of len mentions `Some.Ns.LemFuel.fuel` (FM-ambient: a measure that reads the ambient fuel is not a data measure — it must be an expression over the parameters l)
  Error: Lean backend: the fuel measure of len uses `Some.SizeOf.sizeOf` (FM-sizeOf: Lean's automatic `SizeOf` instances are NONCOMPUTABLE — …)
  ```
  (`neg_fuel_measure_root_ambient`, `neg_fuel_measure_root_sizeof`,
  `neg_fuel_measure_dotted_ambient`, `neg_fuel_measure_dotted_sizeof`; the
  plain forms still refused as before.) The manual's sentence now says
  exactly this (every dotted component; `_root_` refused).
- **M2 (`sorry` passes the suite).** New phase `lean-no-sorry-proofs`
  (`tests/comprehensive/check_no_sorry_proofs.sh`): a comment-stripped,
  vacuity-guarded token scan of `lean-test/*_lemMeasureProofs.lean` and
  `parity/probes/*.proofs.lean` for `sorry`/`admit`/`axiom`/
  `native_decide`/`bv_decide`/`ofReduceBool`/`ofReduceNat`; runs after
  parity (its proofs files in scope) and before the no-numerals gate,
  which stays last. Plant (the `mlen` proof body replaced by `sorry`),
  verbatim:
  ```
  === M2 gate baseline ===
    OK: 4 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
  === M2 plant: sorry for the mlen proof body ===
    FAIL: proof-evading token in a fuel_measure proofs module:
  …/tests/comprehensive/lean-test/Test_fuel_measure_lemMeasureProofs.lean:47:     mlen_lemFuel lemFuel l = mlen l := sorry
  exit 1
  === restored ===
    OK: 4 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
  ```
  Record §2.2, manual, DESIGN, README and the generated obligation
  comment now read: a missing or mistyped theorem fails the build; a
  `sorry`'d theorem is caught by the token gate (lem-lean) and by
  cerberus's sorry/axiom gates.
- **M3 (tally vs table).** Recounted from the table's class column
  (derived): MEASURED 38 / (B) 10 / RESIDUE 17 (tag lookup 6, point-free
  `function` tail 6, evaluation loop 1, client function 1, precondition 1,
  parser 2 — `many`/`many1`, the table's "RESIDUE/(B)" rows, counted as
  residue) / SAME-MODULE 2 = 67. §6.2's tally paragraph corrected and
  labelled as such; design note R3 item 4 corrected; the commit message
  of `d8a17e3` carries the wrong numbers (38/11/16/2) and stays as
  history.
- **M4 (`neg_structural_shadow` passed for the wrong reason).** The probe
  now calls `bad xs` under the shadowing lambda (`List.foldl (fun acc xs
  -> acc + bad xs) 0 [xs]`), EXPECT "not bound by a constructor pattern";
  refused for the shadowing reason, verbatim:
  ```
  Error: Lean backend: 'declare {lean} structural val' refused — no parameter of bad is passed a strict structural subterm (a variable bound by a constructor pattern on that parameter) at every recursive call:
  parameter l: at the self-call File "negative/neg_structural_shadow.lem", line 14, character 50 to line 14, character 55, the argument `xs` is a variable that is not bound by a constructor pattern on that parameter (bound by a lambda or let, or by a match on a computed scrutinee — …)
  ```
- **M5 (cerberus half).** Added to the seam work list as item 8: a gate
  that every `generated/*.lean` is a lakefile root (fail on drift).
- **N1.** The manual states that the syntactic measure rules are
  speedbumps and a disguised parameter-free measure (`l.length - l.length
  + 5`) yields a false, unprovable obligation — the theorem is the
  backstop, by design.
- **N2.** Record §2.2, manual, DESIGN and the generated comment now say
  fuel-STABILITY above the measure (fuel-irrelevance), explicitly "not
  that the exhaustion arm is unreachable".
- **N9 nit.** `parity/expected_failures.txt` now names the OCaml
  binary's text `Failure("int32_of_big_int")` (nat_big_num's wrapper).

Gates on this tree (clean `make clean` then `make lean`, `.tmp/gate3.log`),
verbatim:
```
=== Generation: 51 passed, 0 failed, 0 skipped ===
Build completed successfully (151 jobs).
  OK: inv_fuel_measure.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: 4 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
  OK: 236 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make lean  288.48s user 35.54s system 121% cpu 4:26.09 total
EXIT 0
```
Derived: 72 × `OK (rejected as declared)` (68 + the four M1 probes; the
M4 probe among them), parity 23 OK / 6 both-fail / 4 XFAIL, no other
`FAIL` line. `tests/nonlean-regress/run.sh`: `nonlean-regress: OK (893
artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)`.
The backend change touches only the measure renderer and a generated
comment (Lean target); ocamlyacc unchanged.


## 11. Orchestrator boundary review [AGENT, orchestrator, 2026-09-04]

Independent re-verification of the two-slice branch `arc/structural-declare`
(structural declare + D4 + monotonicity exemplar + fuel-measure declare +
audit response), rebuilt from source in this worktree, three times: at
`020df26` (structural slice), at `d8a17e3` (measure slice) and at
`bf68174` (audit response `dc6a01b` + the audit document `e7796a1`
cherry-picked). Final run, verbatim:

```
Lem bf68174
Build completed successfully (37 jobs).          (lean-lib)
0                                                (grep "^axiom " lean-lib → none)
=== Generation: 51 passed, 0 failed, 0 skipped ===
Build completed successfully (151 jobs).
  OK: 236 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make-lean-rc=0
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
```

(the run's `FAIL` lines are the four registered XFAILs: `f_int_of_big_num`
and `f_int32_overflow` — ruled OCaml-target deviations — and the two F2
strings rows.) Pre-merge audit
`2026-09-04_structural-measure-audit-premerge.md` (MERGE-WITH-FIXES, no
MAJOR → fixed in `dc6a01b`, §10). The OCaml byte-identity of the cerberus
tree was verified by the auditor in a fresh checkout (86/86 files, diff
0) and by the worker; not re-run here. Merge ask goes to the operator on
this head.
