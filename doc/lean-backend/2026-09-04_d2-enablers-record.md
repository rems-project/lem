# D2-enablers slice — record (2026-09-04)

Branch `arc/d2-enablers` (lem-lean, worktree `worktrees/lem-lean-arc/fuel-parameter`),
base mainline `mdd/lean-backend` @ `742506d`. Charter: remove the blocker the
cerberus C1 worker measured at lem `742506d` / cerberus `1b57bcf26` — with the
five numeric budget declares deleted, lem refuses cerberus's sources at four
sites (`ctype.lem:183` `ctypeEqual`, `core.lem:91` `eq_core_base_type`,
`defacto_memory_aux.lem:38` `fake_mem_value_eq`: "fuel'd (or fuel-lifted)
call inside an instance method"; `cmm_op.lem:580` `monStep`: "referenced
outside a fuel scope") — with BACKEND features only, Lean-target only, the
OCaml output byte-identical. Worker [AGENT] (lem-lean); every quoted output
is verbatim from this worktree (`.tmp/` logs named; `.tmp/` is ephemeral);
tallies marked "derived" are derived. Nothing merged, nothing pushed.

## 0. Commits

| Commit | Content |
|---|---|
| `df19cb1` | backend: derived size functions (`t.lemSize`), the `lemSize x` measure form, `[LemFuel]` as an inductive parameter of fuel-reaching indrelns; tests (positive module + proofs + kernel pins, 6 negatives, parity probe + proofs + pin, invariance witness, indreln pins); manual, DESIGN, README, TODO rows 10/15 |
| (the next commit) | this record |

## 1. The ruling this slice implements

[USER 2026-09-04], relayed by the orchestrator: cerberus's `.lem` BODIES are
not restructured (the lem structure is not changed for OCaml's sake); Lean-only
declares are fine; the semantics is a reasoning artifact. So the remedies for
the four D2 sites are backend features, Lean-target only, OCaml
byte-identical — and the sibling rewrite the structural-declare record
demonstrated (D2 demonstration) is ruled out.

## 2. Design

### 2.1 Backend-derived computable size functions (TODO row 15)

**What.** For every RECURSIVE block of generated inductive types in a
non-library module the backend emits, right after the block, in the type's
own module:

```lean
mutual
def ctype_.lemSize (sizex_ : ctype_) : Nat := match sizex_ with
  | .Void0 => 1
  | .Basic _ => 1
  | .Array0 x1 _ => 1 + ctype.lemSize x1
  | .Function (_, x1) x2 _ => 1 + ctype.lemSize x1 + ctype_.lemSize_aux1 x2
  | .FunctionNoParams (_, x1) => 1 + ctype.lemSize x1
  | .Pointer _ x1 => 1 + ctype.lemSize x1
  | .Atomic x1 => 1 + ctype.lemSize x1
  | .Struct _ => 1
  | .Union0 _ => 1
  | .Byte => 1
termination_by structural sizex_
def ctype.lemSize (sizex_ : ctype) : Nat := match sizex_ with
  | .Ctype _ x1 => 1 + ctype_.lemSize x1
termination_by structural sizex_
def ctype_.lemSize_aux1 (sizex_ : List ((qualifiers ×ctype ×Bool))) : Nat := match sizex_ with
  | [] => 0
  | (_, x1, _) :: xs0 => 1 + ctype.lemSize x1 + ctype_.lemSize_aux1 xs0
termination_by structural sizex_
end
```

(verbatim, the cerberus `Ctype.lean` of §4). Classic mechanism name: the
STRUCTURAL SIZE (term-size measure) of a nested inductive, derived in the
derived-comparison machinery's shape (`generate_derived_comparisons`: one
mutual block per type block, one memoized helper per container element
shape, `termination_by structural` on every member that makes a block call;
a member with none is a plain def — Lean 4.28.0/4.32.2 both accept the mixed
block without warnings, probed).

**Why.** A `fuel_measure` over a type defined in the SAME module as the
measured function cannot be a hand-written Lean function (that module must
import the generated one — a cycle; fuel-measure record §2.3), and Lean's
automatic `sizeOf` is NONCOMPUTABLE (`List._sizeOf_inst … has no executable
code`, measured there) while a measured wrapper must execute. The two
cerberus SAME-MODULE rows (`ctypeEqual` over `ctype`, `eq_core_base_type`
over `core_base_type`) had no mechanism; `fake_mem_value_eq` needed a
hand-written cross-module seam (`CerbMeasureMem.mvSize`). All three now
take the derived size (§4).

**The measure syntax: `lemSize x`.** In a `fuel_measure` payload, `lemSize`
applied directly to a PARAMETER `x` is resolved by the backend to
`<Type>.lemSize x` for x's (head-normalised) type — ``declare {lean}
fuel_measure val ctypeEqual = `lemSize c` `` renders `ctypeEqual_lemFuel
(ctype.lemSize c) c c0`. The explicit qualified form `ctype.lemSize c` is
also accepted (it is a qualified global under the existing rules). Rules
(fail-closed, each a probe): `lemSize` must be applied to a parameter
(FM-size-param, `neg_lem_size_notparam`); the parameter's type must be a
generated inductive with a derived size (FM-size-type: a non-inductive
parameter `neg_lem_size_nonind`; a non-recursive type `neg_lem_size_nonrec`;
library/target_rep'd/opaque/Type-1-block types — the census carries the
reason and the message names it). Resolution uses an invocation-wide census
(`St.size_census`, filled by `lean_size_prepass` over EVERY typechecked
module in `lean_analysis_prepass_all` and again per emitted module), so a
measure can name a type from an imported module — `mcount` over `mtree`
from `Test_fuel_measure_types` in the suite; `fake_mem_value_eq` over
`Defacto_memory_types.impl_mem_value` in cerberus. The census and the
emitter run the same analysis (`lean_size_block`) on the same block, so
what a measure resolves to is exactly what is emitted.

Alternatives considered for the syntax: (i) `lemSize x` only — chosen, plus
the qualified form for free (no new declare, no new grammar; the parameter's
type is known to the backend, the user need not know the Lean type name);
(ii) a `declare {lean} size type t` on the type side (TODO row 15's other
option) — a second knob the user must remember, and it cannot help a measure
over a type of a module generated in an earlier invocation unless that
module already carried the declare; rejected. (iii) `t_lemSize` (the brief's
spelling) vs `t.lemSize` — the namespaced form is the derivation's
convention (`t.beq_derived`, `t.ctor_rank_ocaml`) and puts the derived
names where constructors live, so the collision rule is one rule.

**Size semantics** [AGENT decision, the brief left it open]: every
constructor node of the block's types counts 1; every NON-nullary
constructor of a supported container counts 1 (`::`, `some`, `Sum.inl`,
`Sum.inr`) and the nullary ones (`[]`, `none`) 0; tuples are transparent
(component sizes summed); every other field is a LEAF counting 0 — a type
variable (a size over `'a` cannot recurse into `'a`; the brief suggested
counting 1 for these — [AGENT] chose 0 for uniformity with every other leaf:
a leaf's contribution is irrelevant to the recursion-depth bound, which is
all a fuel measure needs), a base type, a type of ANOTHER block (its own
size, if any, is a separate term the user may add: `t.lemSize x + u.lemSize
y`), a function type, a sibling under an unsupported head (`set t`, a user
type applied to `t` — NOT counted: a recursion through such a field is not
bounded by this size, and the sufficiency obligation is where that shows;
cross-block/nested-head counting was NOT built — no consumer needs it; noted
in TODO row 15). Stated precisely (audit NOTE-2, §8): a leaf's WEIGHT is
never what makes a derived size insufficient — a lem `let rec` is
monomorphic, so one recursion cannot descend into an `'a` field; the one
insufficiency class is an unsupported-head field that the SAME recursion
descends into (the auditor's `type tc = TCL | TC of list tc * box tc`
walked on both sides: `tc.lemSize (TC [] (Box [TCL])) = 1`, the wrapper
exhausts loudly inside the box), and there the obligation is unprovable
with the opaque sentinel — the backstop by design. A type recursive ONLY
through such heads gets no size and is refused with that reason (§8
MINOR-1). A list field therefore contributes `length + Σ element
sizes`, so a measure over the parent also bounds a walk along the list
(`ctypeEqual`'s `List.all … (zip params1 params2)` descends one fuel per
element and per child).

**Emission policy — every recursive block, measured.** The brief offered
on-demand emission or every-inductive emission, to be decided by output
size. On-demand is impossible in general: the measure that needs a size may
live in a module generated by a LATER lem invocation (the suite generates
each test file separately; cerberus is one invocation but `Defacto_memory_aux`
measures over `Defacto_memory_types`). Every-inductive is wasteful (a
non-recursive type's size is the constant 1 — a measure over it is the
magic value FM-const refuses). So: every RECURSIVE block (some constructor
field reaches a sibling through tuples/list/maybe/either), all members of
the block (a non-recursive member of a recursive block still gets its
constant-size function: `impl_floating_value.lemSize`). Measured on
cerberus's tree (derived, `grep`/python over `.tmp/cerb/lean-gen`, 170
files): **81 types (27 blocks) of 290 inductives get a size function; 66
container helpers; 1052 lines = 2.69% of the tree's 39110 lines, 55229 bytes
= 1.55% of 3566329 bytes** (CORRECTED per pre-merge audit NOTE-3, §8: the
first version of this sentence said 55205 bytes of 3553252 = 1.6% — those
were Python CHARACTER counts of the UTF-8 text (`→`, `×` are multi-byte),
and the block count stopped before the `end` line; `wc -c` and a
byte-exact recount agree with the auditor's figures.) Not derived: library modules (their regeneration
is out of scope and no library type is a measure target), target_rep'd types
(abbrevs), opaque types, heterogeneous (Type 1, indexed) mutual blocks.

**Collisions** (fail-closed): a constructor of the block, or a field of a
record in the block (mutual-block records render as inductives with
accessor defs `t.<field>`), named `lemSize` or `lemSize_aux…` collides with
the derived names — refused at generation naming the constructor/field
(`neg_lem_size_ctor_collision`, `neg_lem_size_field_collision`). A lem
identifier cannot contain `.`, so a lem VALUE cannot collide with `t.lemSize`.

**Kernel computability and axioms**: `decide` through the sizes on closed
terms and `#print axioms` = none, pinned (`TestLemSizeCheck.lean` §3.1);
`'tm.lemSize' does not depend on any axioms` etc., verbatim from the build.

### 2.2 The instance check and a measured method

Unchanged, and verified both ways: an instance method that references an
AMBIENT fuel'd function is refused (`neg_fuel_instance`, still red as
declared); an instance method that is a MEASURED function is fuel-free and
accepted — `instance (Eq tm) let (=) = tm_eq` and `instance (Sz tm) let sz
t = tm_sum t` in `test_lem_size.lem` render `isEqual := tm_eq` / `sz t :=
tm_sum t` and build; on cerberus the three `Eq` instances render
`isEqual := ctypeEqual` / `eq_core_base_type` / `fake_mem_value_eq` (§4).

### 2.3 Inductive relations in a fuel scope (`monStep`)

(a) Can the referenced function be measured? `cmm_op.lem:543` `monStep pre
s` is `Nondeterminism.pick "monStep" uncommitted_actions >>= fun a -> …` —
it is not fuel'd itself; it is FUEL-LIFTED because `>>=` is `nd_bind`, the
ND monad's bind, census class (B) (ambient by nature: the monad's kill is a
value inside the state function, no data measure exists — fuel-measure
record §6.2 row 56). A measure applies only to a fuel'd function's own
counter, so (a) is impossible for this site.

(b) Built: an inductive relation whose premises reach the ambient (some
relation of the block is in `St.fuel_lifted`) takes `[LemFuel]` as an
inductive PARAMETER, and its premises render inside a fuel scope:

```lean
inductive monTrace  [LemFuel] : (pre_execution) → (incState) → (incState) → Prop where
  | monReflexive : ∀ pre s, ( 
  well_formed_threads_opsem  (pre, empty_witness, [])) → monTrace   pre  s  s
  | monStep : ∀ pre x y z a, (
  monTrace  pre  x  y) → ( 
  nd_mem  ((a : action), z)  (monStep  pre  y)) → monTrace   pre  x  z
```

(verbatim, cerberus `Cmm_op.lean:411-416` of §4). Lean admits an
instance-implicit binder on an inductive (probed on 4.28.0 and 4.32.2 —
`@relB : [LemFuel] → Nat → Nat → Prop`; the constructors' premises resolve
the ambient from the parameter; the recursive occurrence `monTrace pre x y`
takes it by instance resolution). Mechanism: `lean_fuel_prepass` now
registers `Indreln` defs like `Val_def`s (defined = the block's relations,
used = the premises' constants), so a fuel-reaching relation is fuel-LIFTED
— all relations of one indreln block together (one def), a definition that
mentions it takes the binder, and a reference from a fuel-free context (an
assert) is the existing `fuel_scope_check` error (`neg_fuel_indreln_scope`:
"outside a fuel scope"). `clauses` sets `St.fuel_binder` while rendering
such a block and adds ` [LemFuel]` after the free type variables in the
header. Nothing is chosen: the fuel stays the caller's, quantified at the
use (`@monTrace ⟨n⟩ pre x z`; pins `TestFuelParamCheck.lean`: `example :
[LemFuel] → Nat → Nat → Prop := @spin_reach`, a derivation at `⟨5⟩` whose
premise `spin m = 0` the kernel decides). Alternative considered: a
per-rule binder — Lean has no such thing; a `variable [LemFuel]` section —
per-file and fragile (fuel-parameter record §2 (c)); restating the model —
forbidden by the ruling.

## 3. Before / after — one function, verbatim

`tests/comprehensive/test_lem_size.lem`, `tm_eq` (the D2 shape: `List.all
(fun …) (List.zip …)` AS WRITTEN, an `Eq` instance's method). BEFORE (the
opam-installed lem `742506d`, on the type + `tm_eq` + `instance (Eq tm)`
without the measure line — `.tmp/before/before2.lem`): generation REFUSED —

```
File "before2.lem", line 17, character 13 to line 17, character 17
  Error: Lean backend: fuel'd (or fuel-lifted) call inside an instance method (unsupported: instance fields cannot take the [LemFuel] binder)
  original input: "tm_eq"
```

(the message the C1 worker measured at `ctype.lem:183`); with the measure
line, lem `742506d` refuses `lemSize` as a free variable (FM-free) — the
form did not exist. AFTER, at this lem, with
``declare {lean} fuel_measure val tm_eq = `lemSize t1` `` (`Test_lem_size.lean`):

```lean
def tm_eq ( t1 : tm) ( t2 : tm) : Bool := tm_eq_lemFuel (tm.lemSize t1)  t1  t2
theorem tm_eq_lemFuel_zero ( t1 : tm) ( t2 : tm) :
    tm_eq_lemFuel 0  t1  t2 = (fuelExhausted false) := rfl
instance   : Eq0 tm where
    isEqual   :=  tm_eq
    isInequal   :=  fun  a  b =>  not  (tm_eq  a  b)
```

and the obligation in `Test_lem_size_auxiliary.lean`, proved in
`Test_lem_size_lemMeasureProofs.lean` (strong induction on `tm.lemSize`, a
child's size below its parent's over the derived list helper
`tm.lemSize_aux1`, `List.all` congruent in the per-element function,
`LemLibTheorems.lemListZip_eq` bridging `lemListZip` to `List.zip`), verbatim
from the build:

```
info: Test_lem_size_lemMeasureProofs.lean:212:0: 'Test_lem_size_lemMeasureProofs.tm_eq_measure_sufficient' depends on axioms: [propext, Quot.sound]
```

The worker is byte-identical to the ambient form; the OCaml output is
untouched (§5 invariance).

## 4. The cerberus generation + build check (scratch, read-only sources; `.tmp/cerb`)

### 4.1 Setup

- Sources: `frontend-orig` = cerberus `1b57bcf26:frontend/` (`git archive`
  from the cerberus worktree, read-only); `frontend-c1` =
  `wip/fuel-parameter-C1-scratch:frontend/` (the C1 worker's tree: the five
  numeric declares deleted, 19 `fuel_consumer` declares in `mem.lem`);
  `frontend-c1d` = `frontend-c1` + exactly three lines, each directly after
  the val's existing sentinel declare (the last lines of the files):

  | file:line | text |
  |---|---|
  | `frontend/model/ctype.lem:428` | ``declare {lean} fuel_measure val ctypeEqual = `lemSize c` `` |
  | `frontend/model/core.lem:473` | ``declare {lean} fuel_measure val eq_core_base_type = `lemSize bTy1` `` |
  | `frontend/model/defacto_memory_aux.lem:469` | ``declare {lean} fuel_measure val fake_mem_value_eq = `lemSize mval1` `` |

  (`c` is `ctypeEqual`'s first parameter AFTER lem's pattern compilation —
  the source binds `(Ctype _ ty1)`; the fuel-measure record §2.1's rule.
  Line numbers are those of the INSERTION described — directly after the
  val's sentinel declare, which in `defacto_memory_aux.lem` is line 468,
  followed by `simplify_integer_value_base`'s sentinel at 469 in the
  original; so the new line is 469 and the file grows to 470. The auditor
  APPENDED the same line after the last line and got `:470` (NOTE-3);
  either placement is a Lean-only declare and the OCaml output is
  byte-identical in both — re-verified on a fresh copy, `.tmp/cerb2`: the
  three declares at `ctype.lem:428`, `core.lem:473`,
  `defacto_memory_aux.lem:469`.)
- Baseline lem: `git archive 3c88f0d` built in `.tmp/cerb/lem-base`
  (`make build-lem`); its `-v` prints `Lem 742506d` because the version
  target reads the ENCLOSING worktree's git HEAD (the archive is not a
  repo) — the source is `3c88f0d`, checked: `lem-base source == 3c88f0d
  src/lean_backend.ml` (`diff` against `git show 3c88f0d:src/lean_backend.ml`
  empty). New lem: this worktree's `./lem` (`Lem 742506d-dirty`).
- Flags/lists: the cerberus Makefile's exactly (`make --eval` in the
  cerberus primary, read-only): `-wl ign -wl_rename warn -wl_pat_red err
  -wl_pat_exh warn -cerberus_pp`; `LEM_SRC` 86 files, `LEM_SRC_LEAN` 85,
  `LEAN_HANDWRITTEN` 23.

### 4.2 OCaml byte-identity — verbatim (`.tmp/cerb/gen-run.log`)

```
ocaml-base-orig exit 0
ocaml-new-c1 exit 0
ocaml-new-c1d exit 0
files: base-orig=86 new-c1=86 new-c1d=86
OCAML DIFF base-orig(lem 3c88f0d) vs new-c1d(new lem, C1 sources + 3 fuel_measure declares): exit 0 lines 0
OCAML DIFF new-c1 vs new-c1d (the 3 declares alone): exit 0 lines 0
```

`diff -r` of the 86-file trees, both empty: lem `3c88f0d` on the ORIGINAL
sources (numeric declares and their comments still present) and this lem on
the C1 sources plus the three new declares produce the same OCaml, byte for
byte.

### 4.3 Lean generation — the four sites, verbatim

```
LEAN GEN exit 0 files 170
```

(`lean-gen.log`: warnings only — the pre-existing non-exhaustive-match
warnings and the `renaming 'Error' to 'Error0'` note; 0 errors.) The
cerberus sources generate at this lem with ONLY Lean-only declares added:
no sibling rewrite, no rule removed. The four sites:

```
lean-gen/Ctype.lean:442:def ctypeEqual (c : ctype) (c0 : ctype) : Bool := ctypeEqual_lemFuel (ctype.lemSize c) c c0
lean-gen/Ctype.lean:449:    isEqual    :=  ctypeEqual
lean-gen/Core.lean:222:def eq_core_base_type ( bTy1 : core_base_type) ( bTy2 : core_base_type) : Bool := eq_core_base_type_lemFuel (core_base_type.lemSize bTy1)  bTy1  bTy2
lean-gen/Core.lean:228:    isEqual   :=  eq_core_base_type
lean-gen/Defacto_memory_aux.lean:70:def fake_mem_value_eq ( mval1 : impl_mem_value) ( mval2 : impl_mem_value) : Bool := fake_mem_value_eq_lemFuel (impl_mem_value.lemSize mval1)  mval1  mval2
lean-gen/Defacto_memory_aux.lean:77:    isEqual   :=  fake_mem_value_eq
```

and `monTrace` (§2.3). Census (derived, `grep`): `[LemFuel]` binders 397
(the C1 record's scratch tree: 396 — `monTrace`'s parameter is the +1);
ambient wrappers `_lemFuel LemFuel.fuel` 64; measured wrappers 3.

### 4.4 The build — verbatim (`.tmp/cerb/lean_frontend/build-1.log`)

Package: `generated/` = the 170 generated files + the 23 hand-written seams
from `wip/fuel-parameter-C1-scratch:lean_frontend/` (`git show`, read-only;
the Makefile's `import Operators` sed applied to `Core_run.lean`); the WIP
`lakefile.toml` with FOUR scratch changes (`diff lakefile.toml.wip
lakefile.toml`): `LemLib` from `git`/`rev` to `path = "../lean-lib-copy"` (a
copy of this tree's `lean-lib` without `.lake` — a path dependency shares
its `.lake` with whoever builds it, and the suite's 4.28.0 and cerberus's
4.32.2 must not trash each other's oleans); the three auxiliary roots whose
obligations have no proofs module yet DROPPED (`Ctype_auxiliary`,
`Core_auxiliary`, `Defacto_memory_aux_auxiliary` — §6); `Main` added as a
lib root (the exe root compiles without linking `native/md5.o`); the
`[[lean_exe]]` sections removed and `defaultTargets = ["CerberusLean"]`.
Lean 4.32.2 (cerberus's `lean-toolchain`), `CERB_MEM_MAX=16G`:

```
⚠ [90/223] Built Ctype (663ms)
⚠ [143/223] Built Defacto_memory_types (4.0s)
⚠ [152/223] Built Defacto_memory_aux (1.0s)
⚠ [157/223] Built Cmm_op (1.7s)
⚠ [161/223] Built Core (6.6s)
⚠ [222/223] Built Main (11s)
Build completed successfully (223 jobs).
CERB_MEM_MAX=16G  lake build CerberusLean  393.95s user 40.36s system 155% cpu 4:38.88 total
```

`grep -c "error:"` = 0; the ⚠ lines are the pre-existing derived-comparison
`unused termination_by`/deprecation warnings (64 modules with warnings, 156
clean). So: the whole tree — the 81 derived size blocks, the three measured
`Eq` methods, `monTrace [LemFuel]`, and the C1 seams (`CerbND`, `CerbMem`,
`Main` with `--fuel`) — compiles against LemLib at this lem. What this build
does NOT check: the three new obligations (their auxiliary roots dropped — no
proofs, no `sorry`, §6) and the runtime (the differential lanes are the
cerberus half's).

### 4.5 C1's checklist (the Lean-only declares the real tree needs at this lem)

1. Delete the five numeric declares (done on the WIP branch:
   `driver.lem:1910-1918`, `nondeterminism.lem:569-574`).
2. The 19 `declare {lean} fuel_consumer val` lines in `frontend/model/mem.lem`
   (done on the WIP branch; C1 record §3 row 4): `allocate_object`,
   `allocate_region`, `load`, `store`, `ne_ptrval`, `diff_ptrval`,
   `validForDeref_ptrval`, `isWellAligned_ptrval`, `array_shift_ptrval`,
   `member_shift_ptrval`, `eff_array_shift_ptrval`, `eff_member_shift_ptrval`,
   `memcpy`, `memcmp`, `realloc`, `copy_alloc_id`, `offsetof_ival`,
   `sizeof_ival`, `alignof_ival`.
3. The three `fuel_measure` lines of §4.1 (NEW; inserted directly after
   each val's sentinel declare they sit at `ctype.lem:428`, `core.lem:473`,
   `defacto_memory_aux.lem:469`; appended at end of file the third is
   `:470` — either is fine).
4. Nothing for `monStep`/`monTrace`: the backend emits `inductive monTrace
   [LemFuel]` from the unchanged source.
5. Then: the three obligation proofs modules `Ctype_lemMeasureProofs.lean`,
   `Core_lemMeasureProofs.lean`, `Defacto_memory_aux_lemMeasureProofs.lean`
   (hand-written seams, manifest + lakefile roots), each with the stated
   theorem — the template is `Test_lem_size_lemMeasureProofs.lean`'s
   `tm_eq` (the same `List.all (fun …) (List.zip …)` shape; `ctypeEqual`
   also descends through `paramsEqual`'s lambda and `qualifiersEqual`;
   `fake_mem_value_eq`'s exhaustive `error` arm is a `failwithI` leaf). The
   obligations as generated (`Ctype_auxiliary.lean:45`, verbatim):
   ```
   theorem ctypeEqual_measure_sufficient (c : ctype) (c0 : ctype) (lemFuel : Nat) (lemMeasureLe : (ctype.lemSize c) ≤ lemFuel) :
       ctypeEqual_lemFuel lemFuel c c0 = ctypeEqual c c0 :=
     Ctype_lemMeasureProofs.ctypeEqual_measure_sufficient c c0 lemFuel lemMeasureLe
   ```
   Until they exist those three auxiliary modules do not build (fail-closed,
   by design of the fuel-measure slice).
6. Re-pin `lakefile.toml` to the merged lem head; `lake update LemLib`;
   regenerate; the lem-sync stamp records.

## 5. Gates — verbatim

### 5.1 tests/comprehensive `make lean` (clean: `make clean` then `make lean`; `.tmp/gate-suite-1.log`)

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
  [78 × "OK (rejected as declared)" — derived count; the 6 new probes among them]
  OK: inv_fuel.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_fuel_measure.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_lem_size.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_reader_consumer.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_structural.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_supply.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
  [parity: 24 × "OK: parity" (the 23 before + p_lem_size), 6 × "OK: both fail", 4 × XFAIL (the registered f_int_of_big_num, f_int32_overflow, p_str_bytes, p_str_escapes) — derived counts]
  OK: 6 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
  OK: 242 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make lean  497.78s user 46.60s system 110% cpu 8:10.45 total
EXIT 0
```

`p_lem_size`'s first run (`REBASELINE=1 ./parity/run.sh p_lem_size`, recording
the OCaml reference pin), verbatim: `REBASELINED pin
…/parity/expected/p_lem_size.out` / `OK: parity (4 lines byte-identical to the
OCaml reference; pin matches)`; the pin reads `psum leaf: 7` / `psum empty
node: 0` / `psum tree: 11` / `psum chain 300: 1`.

A first clean run of the suite (`.tmp/gate-suite-1.log`) FAILED at the
invariance phase (`inv_structural.lem`/`inv_supply.lem` "did not
generate", `EXIT 2`) because I had started `make build-lem` (which removes
and rebuilds `src/main.native`, the `lem` symlink's target) CONCURRENTLY to
surface compiler warnings — my own interference, not a defect; recorded so
the two logs are not confused. The run above is the clean re-run with
nothing else on the box.

### 5.2 tests/nonlean-regress (`.tmp/nonlean-1.log`)

```
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
EXIT 0
```

No rebaseline: the backend change is Lean-emission-only (no grammar change,
no library edit); the invariance witness `inv_lem_size.lem` passes with the
four non-Lean emitters byte-identical with and without the declares.

### 5.3 lean-lib

Untouched by this slice (no LemLib change; the suite's `lake build` of the
package is in §5.1's run).

### 5.4 The new negatives (6, in the run above)

`neg_lem_size_nonind` (FM-size-type: a `nat` parameter), `neg_lem_size_nonrec`
(a non-recursive type: "non-recursive type"), `neg_lem_size_notparam`
(FM-size-param: `lemSize (t)`), `neg_lem_size_ctor_collision`,
`neg_lem_size_field_collision` ("collides with the backend-derived size
function"), `neg_fuel_indreln_scope` (an assert on a fuel-parametric
relation: "outside a fuel scope"). Negative probes total: 78 `OK (rejected
as declared)` (72 + 6; derived count).

## 6. Decisions for the operator

1. **Leaf contribution 0** (incl. type variables — the brief said "count
   1" for those): [AGENT] chose uniform leaves = 0 (a leaf's contribution
   is irrelevant to the depth bound). A one-line change if 1 is preferred;
   the pins and proofs would move.
2. **Every recursive block, not on demand** — measured at 1.6% of the
   cerberus tree's bytes (§2.1). If the operator prefers on-demand within
   an invocation plus a type-side declare for the cross-invocation case,
   both are small; the census machinery is shared.
3. **The three cerberus obligations** (§4.5 item 5) are C1's/C2's work: the
   design's fail-closed promise is exactly that the auxiliary modules do
   not build without them. The scratch build here dropped those three
   roots to demonstrate the rest of the tree; a real tree cannot.
4. **Cross-block / unsupported-head counting** in sizes is not built (leaf
   0); a measure can add the other block's size explicitly. Fund only if a
   census row needs it (none of the 67 does).

## 7. Not done, and why

- The three cerberus obligation proofs (the cerberus half's; §4.5).
- Cross-block counting in derived sizes (§6 item 4).
- TODO row 17 (point-free tails) is untouched — a different mechanism
  (eta-expansion or measure-by-position), not on this slice's path.
- The Ott derived artifacts (TODO row 5, pre-existing; no grammar change
  here anyway).
- `.tmp/` (baseline lem, the cerberus copies and trees, the probe package,
  logs) is ephemeral and deleted at slice end; everything load-bearing is
  quoted above.

## 8. Audit response (pre-merge audit `2026-09-04_d2-enablers-audit-premerge.md` @ `145f453`, verdict MERGEABLE, no MAJOR)

One commit on `arc/d2-enablers` (this section's), on top of the
orchestrator's TODO-row-18 commit `f258c2c`. Each item, what changed, and
the evidence (verbatim from this worktree).

- **MINOR-1 (recursive only through an unsupported head refused as
  "non-recursive").** `lean_size_block` now distinguishes three cases: some
  field reaches a sibling through tuples/`list`/`maybe`/`either` (a size is
  derived); no field references a sibling at all ("a non-recursive type …",
  unchanged); a sibling is referenced but only under heads the derivation
  cannot count — NEW reason with the remedy. Probe
  `neg_lem_size_unsupported_head` (the auditor's `box tb`), verbatim:
  ```
  Error: Lean backend: the fuel measure of tbcount uses `lemSize t`, but the type of t (Neg_lem_size_unsupported_head.tb) has no derived size function (FM-size-type: it is a type recursive ONLY through an unsupported container head (a `set`, a `map`, a user type applied to the recursive type, a function type — the derivation counts siblings only through tuples, `list`, `maybe` and `either`), so no derived size bounds its recursion; write a hand-written computable size in a Lean module the generated module imports (`declare {lean} extra_import`) and name it qualified in the measure); a size is derived for every recursive block of generated inductive types in a user module (`t.lemSize`)
  ```
  (`neg_lem_size_nonrec` still reads "it is a non-recursive type (its size
  is the constant 1 …)".)
- **MINOR-2 (target_rep'd type's reason unreachable).** Cause found: a type
  with a Lean target_rep reaches the backend as a `Comment`-wrapped
  `Type_def` (the target's def_trans comments it out; the emitter renders
  the abbrev from the `Comment` case), and `lean_size_prepass` did not walk
  into `Comment` — so the census had no entry and the generic "not a
  generated inductive type of this invocation" fired. The prepass now walks
  `Comment c`. Probe `neg_lem_size_reptype` (the auditor's `rt`), verbatim:
  ```
  Error: Lean backend: the fuel measure of rspin uses `lemSize r`, but the type of r (Neg_lem_size_reptype.rt) has no derived size function (FM-size-type: it is a type with a Lean target_rep (rendered as an abbrev of a hand-written type)); a size is derived for every recursive block of generated inductive types in a user module (`t.lemSize`)
  ```
  The docs' sentence is now true as written. (The library reason stays
  unreachable by construction — a library type is never a user module's
  `Type_def`; a `list nat` parameter is the "not a generated inductive
  type" message, correct for it.)
- **MINOR-3 (manual: a `lemma` referencing fuel "is refused").** False, as
  measured by the auditor: every lem `lemma`/`theorem` renders as `/-
  removed theorem … -/` (pre-existing). The manual's sentence now says so
  and lists the real fuel-scope sites (an `assert`; instance methods;
  relations take the binder).
- **NOTE-1 (a parameter named `lemSize` listed as usable).** The
  FM-size-param message now filters it out and names the cause. Probe
  `neg_lem_size_param_named`, verbatim:
  ```
  Error: Lean backend: `lemSize` in the fuel measure of spin must be applied directly to one of the parameters n (FM-size-param: `lemSize x` — the backend resolves x's type to its derived size function `t.lemSize`; any other argument shape is refused; `lemSize` is a reserved word inside a measure, so the PARAMETER named `lemSize` cannot be mentioned there — rename it)
  ```
  The manual's derived-sizes paragraph gains the reserved-word clause.
- **NOTE-2 (the insufficiency class).** Stated in DESIGN.md's totality
  paragraph and in §2.1 above: leaf weight is irrelevant; the one
  insufficiency class is an unsupported-head field the same recursion
  descends into; the obligation is the backstop (unprovable with the opaque
  sentinel).
- **NOTE-3 (tallies; line number).** Recounted byte-exactly on a fresh
  regeneration (`.tmp/cerb2`, this lem, the C1 sources + 3 declares, 170
  files): `wc -c` **3566329 bytes**, 39110 lines; size blocks 27 (20
  `mutual`), **55229 bytes = 1.55%**, 1052 lines = 2.69%; 81 `.lemSize`
  defs, 66 helpers. The auditor is right: my 3553252 / 55205 were Python
  CHARACTER counts (`len(str)` of UTF-8 text with `→`/`×`) and my block
  regex stopped before the `end` line; §2.1 corrected and labelled. The
  line number: `:469` is right for the placement the record describes
  (inserted directly after the sentinel declare at 468); the auditor's
  appended variant is `:470`; §4.1/§4.5 now say both.
- **NOTE-6 (invariance harness false-positive shape).** Noted in the
  `lean-invariance` header of `tests/comprehensive/Makefile`: an `assert`
  after a stripped declare shifts its OCaml `run_test` location string;
  keep asserts before the declares (none of the six witnesses has one).
- NOTE-4/5/7/8: no action (verified checklist; pre-existing limitations;
  the version-stamp caveat already in §4.1; relation gathering order).

Negative probes after this commit: 81 `OK (rejected as declared)` (78 + 3;
derived — `neg_lem_size_param_named`, `neg_lem_size_reptype`,
`neg_lem_size_unsupported_head` among them). Gates on this tree, each run
ALONE on the box (a first pair of runs overlapped each other — a background
suite run I believed dead was still going when I started its replacement,
and the two non-Lean-net runs shared `.scratch` (one tripped the vacuity
guard, the other showed duplicated exit rows) — discarded, not evidence;
the solo re-runs are the ones quoted). `make clean` then `make lean`
(`.tmp/gate-suite-5.log`), verbatim:
```
=== Generation: 52 passed, 0 failed, 0 skipped ===
info: Test_lem_size_lemMeasureProofs.lean:211:0: 'Test_lem_size_lemMeasureProofs.tm_sum_measure_sufficient' depends on axioms: [propext, Quot.sound]
info: Test_lem_size_lemMeasureProofs.lean:212:0: 'Test_lem_size_lemMeasureProofs.tm_eq_measure_sufficient' depends on axioms: [propext, Quot.sound]
info: Test_lem_size_lemMeasureProofs.lean:213:0: 'Test_lem_size_lemMeasureProofs.mcount_measure_sufficient' depends on axioms: [propext, Quot.sound]
info: Test_lem_size_lemMeasureProofs.lean:214:0: 'Test_lem_size_lemMeasureProofs.sb_count_measure_sufficient' depends on axioms: [propext, Quot.sound]
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
  [81 × "OK (rejected as declared)" — derived count]
  OK: inv_fuel.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_fuel_measure.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_lem_size.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_reader_consumer.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_structural.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_supply.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
  [parity: 24 × "OK: parity", 6 × "OK: both fail", 4 × XFAIL (the registered four) — derived counts]
  OK: 6 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
  OK: 242 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make lean  315.67s user 37.34s system 121% cpu 4:50.65 total
EXIT 0
```
`tests/nonlean-regress/run.sh` (`.tmp/nonlean-4.log`), verbatim:
```
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
./tests/nonlean-regress/run.sh  205.89s user 8.95s system 83% cpu 4:16.91 total
EXIT 0
```
No rebaseline; the diff touches only `src/lean_backend.ml` (Lean target),
three negative probes, docs and a Makefile comment.


## 9. Orchestrator boundary review [AGENT, orchestrator, 2026-09-04]

Independent re-verification of `arc/d2-enablers`, lem rebuilt from source
in this worktree, twice: at `22aa0fb` (the slice) and at `1c5349c` (audit
response `bc5e04a` + the audit document `145f453` cherry-picked). Final run,
verbatim:

```
Lem 1c5349c
=== Generation: 52 passed, 0 failed, 0 skipped ===
  OK: 242 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make-lean-rc=0
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
```

(lean-lib `Build completed successfully (37 jobs)`, zero axioms, and the
four registered XFAILs, as in the previous runs.) Pre-merge audit
`2026-09-04_d2-enablers-audit-premerge.md` (MERGEABLE, no MAJOR; the three
MINORs fixed in `bc5e04a`, §8). The cerberus OCaml byte-identity was
verified by the worker and reproduced three ways by the auditor; not
re-run here. Merged ff-only on the operator's standing authorisation for
this branch ([USER 2026-09-04] authorised the merge once the fixes landed).
