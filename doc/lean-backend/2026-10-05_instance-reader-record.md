# Instance-implicit readers: record (2026-10-05)

Branch `arc/pnvi-switches`, from lem mainline `mdd/lean-backend` = `4e70bb5`
(the current Cerberus pin). This is slice S0 of the Cerberus PNVI-ae-udi
arc. It adds a generic lem-lean mechanism; Cerberus itself is not
touched (S1 uses the mechanism).

## 1. Why, and provenance

The governing design is the Cerberus record
`lean_frontend/docs/2026-10-04_pnvi-ae-udi-design.md` (§B.0, §B.3, §B.6,
§E row S0), in the design worktree at commit `aa5df9201`. Its option 3
threads the Cerberus switch set as an instance-implicit ambient parameter
`[CerbGlobal.Switches]`, in the `[LemFuel]` shape. The aim is that no
positional signature changes in the consumer.

The operator's ruling on that record is recorded in its §1.4 as
[USER 2026-10-05]: agreement with the PNVI recommendations, except that
mirroring crashes or obviously wrong behaviour should be refusals.
The coordinator's reading, also recorded there, is that this accepts
option 3 with S0 in lem-lean included. The orchestrator's brief for this
slice restates it as "[USER 2026-10-05] accepted option 3".

Every design choice below that the brief did not fix is marked [AGENT].

## 2. The mechanism

### Classic name

The mechanism is an **implicit parameter**: the environment of a reader
monad, passed by type-class (instance) resolution. This is the shape of
Haskell's implicit parameters (Lewis, Launchbury, Meijer and Shields,
POPL 2000) and of Lean's own ambient-configuration classes.

Measured against the existing backend mechanisms, it is:

- the explicit reader lifting with a different binder kind; or
- the fuel lifting with a class that the user names.

### Syntax [AGENT]

```lem
declare {lean} reader val r = instance `Cls.field`
declare {lean} reader_consumer val f = instance r
```

**Reader form.** The constant `r : unit -> T` becomes an instance reader:

- The backticked text is the projection of a one-field Lean class that
  the consumer writes by hand (`class Cls where field : T`).
- The class is the part of that text before the last dot.
- A read `r ()` emits `Cls.field`.
- A bare reference to `r` emits `(fun (_ : Unit) => Cls.field)`.

**Consumer form.** It marks a target_rep'd `f` whose hand-written
implementation binds `[Cls]` itself:

- No argument is passed at `f`'s call sites.
- `f`'s callers bind `[Cls]`.
- A consumer may read several instance readers; declare it once per
  reader.

**Why this syntax.**

- **House form.** Every lem-lean declaration has the form
  `declare {targets} <role> val <name> [= <payload>]` (`fuel`,
  `ground_rep`, `fuel_measure`).
- **Same roles, different binder.** The instance reader is the existing
  `reader` role with a different binder kind, and its consumer is the
  existing `reader_consumer` role. So the instance form is a payload on
  those two roles, not two new role keywords.
- **No new reserved word.** `instance` is already a lem keyword, so the
  lexer is unchanged and nothing changes for non-Lean users.
- **Why the projection, not the class.** The payload is the text that
  appears at every read site, the analogue of `LemFuel.fuel`. Naming only
  the class, as in §B.3's example
  ``reader_binder switches = instance `CerbGlobal.Switches` ``, would
  leave the read site without a field name. The alternatives were worse:
  `(inferInstance : Cls).1` is ugly in goals, and a second backticked
  field-name payload needs more grammar.
- **Projection rules.** Lean names a structure's projections `Cls.field`,
  so the class prefix is determined. The text must be at least two
  dot-separated plain identifiers (IR-proj).
- **Per-reader consumers.** The explicit `reader_consumer` passes all
  readers, because its arguments are positional. Nothing forces that
  here, so the consumer names its reader. A def that reaches only one
  instance reader then binds only that reader's class.

For Cerberus S1 this reads:

```lem
declare {lean} reader val switches = instance `CerbGlobal.Switches.switches`
declare {lean} reader_consumer val load = instance switches
```

### Lifting

The lifting is the same transitive fixpoint as the explicit reader's and
the fuel's (`lean_ireader_prepass`). A definition binds a reader's class
if it does any of the following:

- reads that instance reader;
- calls a consumer of it;
- calls a definition that binds it.

The fixpoint runs per definition: `St.ireader_lifted` maps each
definition to its readers, in the global reader order. Its scope follows
the fuel prepass:

- Granularity is the `Val_def`, and nested modules are recursed into.
- Instances are skipped.
- target_rep'd definitions are skipped (their bodies are dead text).
- `reader_seed` definitions are included.

Two further points:

- **Call sites are unchanged.** Lean's instance resolution passes the
  binder along, so no call site needs a rewrite, and bare or higher-order
  references need no repair.
- **Imports.** The projection is target text, like a target_rep. The
  class's module (the first dotted component) is imported by the same
  heuristic `collect_cr_simple_import`.

### No instance anywhere

LemLib and the generated code contain no instance, by design; this is
the fuel rule.

- The entry point supplies the instance, either as `@f ⟨v⟩ …` or as
  `letI : Cls := ⟨v⟩`.
- A theorem quantifies over it by binding `[Cls]`.
- `@f ⟨v⟩` unfolds by `rfl`.

The tests declare no instance either. Every pin supplies its own.

The backend has no code path that emits an `instance` for these classes.
As evidence, a grep for instance declarations was run over the generated
`Test_instance_reader.lean`, its auxiliary file and
`TestInstanceReaderImpl.lean`. The pattern was `^\s*(@[...])?(instance|def inst)`,
`letI`, or `: Cls :=`. It matched comment lines only.

### Binder order [AGENT]

Every emitted piece uses the same order:

1. type variables and class constraints;
2. `[LemFuel]`, where the fuel lifting puts it;
3. **the instance readers' `[Cls]` binders**, in the global order;
4. `[Inhabited tv]`;
5. the fuel counter (workers only);
6. the explicit reader binders;
7. the supply binders;
8. the arguments.

The pieces this covers are: definitions, multi-clause equation groups,
`Let_def` values (including a destructuring let's private right-hand-side
definition and its projections), fuel workers, wrappers (ambient and
measured), `_zero` lemmas and measure obligations.

The global order sorts instance readers by their lem name, then by path.
So `@f ⟨n⟩ ⟨v⟩ …` instantiates the fuel first, then the instance readers.
This position is the one the binder takes in the fuel lifting.

### Interactions

**`reader_seed`.**

- A seed cuts EXPLICIT readers only.
- A seed definition is an ordinary member of the instance fixpoint, so an
  instance reader propagates through it: the seed definition binds
  `[Cls]` itself.
- Its N positional seeds count explicit readers only.
- Instance readers are not seedable.

Pinned by `seed_entry` (`[Sw] → Nat → Nat → Nat`), `via_seed`
(`[Sw] → Nat → Nat`) and `seed_plain`. `seed_plain` is a seed definition
with no instance reach, and it stays unbound.

**Mutual blocks.**

- A mutual definition is one defined set, so its members bind
  all-or-none. This is the composition the fuel/reader record
  `2026-09-20_fuel-mutual-reader-record.md` established for explicit
  readers.
- Pinned by a structural pair where only one member reads (`iev`/`iodd`,
  both `[Sw]`) and a fuel'd pair where both read (`rping`/`rpong`).
- **The fuel worker binds `[Cls]` whenever its group does.** The fuel
  worker binds `[LemFuel]` only when it passes the ambient on. The class
  is different: the body reads it, and there is no counter to stand in
  for it.

**Explicit readers.**

- Explicit readers are unchanged. Their lists, binder names, sorting,
  seed counting and consumer injection read `cd.reader` /
  `cd.reader_consumer` only, and those fields are never set by the new
  forms.
- A val may be an explicit `reader_consumer`, an instance consumer and a
  `fuel_consumer` at once. This is the Cerberus memory-operation shape,
  pinned by `uses_both_c : [LemFuel] → [Sw] → Nat → Nat → Nat`, where the
  explicit reader is still the leading explicit argument.

**Fuel, measures and supply.**

- `mixed` is a fuel'd definition that reads an explicit reader and the
  instance reader.
- `ilen` is a measured definition. Its obligation binds `[Sw]` and is
  proved in `Test_instance_reader_lemMeasureProofs.lean`.
- `draw_sw` is a supply-lifted definition, typed
  `[Sw] → Nat → Unit → (Nat × Nat) × Nat`.

### Fail-closed rules

**Scope net (`ireader_scope_check`).** This is checked at every
application, bare reference and infix use. It fires on a read of an
instance reader, or a reference to a member or consumer, where its
`[Cls]` is not in scope. That covers instance methods, inductive relation
rules and lem `assert`s. It is a generation-time error naming the site
and the missing class; there is no default.

**Declaration checks (`lean_ireader_check`).** These run for every marked
constant, even if unused:

- **IR-proj:** the projection is not at least two plain dotted
  identifiers (no guillemets, spaces or `_root_`).
- **IR-type:** the reader's type is not `unit -> T`, or it has free type
  variables (`forall 'a. unit -> 'a`): the class field has one type
  (review F2).
- **IR-inline:** the reader has an inline Lean representation
  (`let inline`). The inline macro replaces every read before emission,
  so the read would silently become the body and the reading definition
  would not even bind the class (found while fixing review F1).
- **IR-body** (checked in the pre-pass, at the definition): the reader
  has a lem definition but no Lean target_rep. It would be emitted as
  `def r [Cls] (u : Unit) : T := <body>`, and hand-written Lean calling
  `r` would get the body, not the instance (review F1).
- **IR-class:** two readers share a class. They would read the one
  instance and silently conflate. The class text is not resolved at
  generation, so the check is syntactic, and since review F3 it compares
  the classes' LAST dotted components, not the whole texts [AGENT]. See
  "IR-class and name resolution" below.
- **IR-mix:** the reader is also an explicit `reader`, a `reader_seed`, a
  `supply`, a `reader_consumer`, a `fuel_consumer`, `fuel`, or an
  instance consumer.
- **Redeclaration:** a second projection for the same target is refused
  in typecheck, rather than overwriting the first.
- **IRC-reader:** a consumer names a constant that is not an instance
  reader.
- **IRC-rep:** a consumer has no Lean target_rep.
- **IRC-mix:** a consumer is also a reader, a `reader_seed` or a
  `supply`.

### IR-class and name resolution (review F3)

The review's F3 said the guard compares class names syntactically, so
`Impl.Sw.sw` and `_private.Impl.Sw.sw` count as two classes, and that
Lean then fails loudly. The first half was right. The second half holds
for that example, because `_private.Impl.Sw` names no class and Lean
reports an unknown identifier. It does NOT hold in general.

- **Measured (Lean 4.32.2, scratch files).** Lean name resolution can
  make two different texts name one class: `Sw` under `open Impl`, or
  inside `namespace Impl`. Two instance binders of one class are legal
  Lean, and every read takes the innermost one. With `class Impl.Sw`,
  `open Impl` and
  `def both [Impl.Sw] [Sw] (x : Nat) : Nat := Impl.Sw.sw + Sw.sw + x`,
  the file compiled and `#eval @both ⟨1⟩ ⟨10⟩ 0` printed `20`; the same
  def inside `namespace Impl` also printed `20`. Both reads silently took
  the second instance. (An `export Impl (Sw)` alias `B.Sw` and an
  `abbrev Sw2 := Impl.Sw` were loud: the reads `B.Sw.sw` and `Sw2.sw`
  failed with `Unknown constant`.) [Note 2026-10-08, delta audit A-1:
  these measurements predate the tightening below. Under the tightened
  check, `B.Sw` and the review's `_private.Impl.Sw` end in `Sw`, so as
  the class of a second reader beside `Impl.Sw` they are refused at
  generation and never reach Lean. Only the `abbrev` case is still a
  Lean-build failure (see "Residual").]
- **Fix [AGENT].** Namespaces and `open` never change a name's last
  component. So IR-class now refuses two instance readers whose
  classes have the same LAST dotted component, with a message naming
  both classes. Probe: `neg_ireader_class_alias` (`NegImpl.Sw.sw` and
  `Sw.sw`). The cost is that two genuinely different classes `A.Sw` and
  `B.Sw` cannot both be instance-reader classes; renaming one is the
  remedy. Under the brief, F3 was documentation-only. This tightening goes
  beyond that, because the measured behaviour is a silent conflation;
  it is fail-closed and reversible, and it is flagged for review.
- **Residual.** A class reached under a different last component (an
  `abbrev` of a class) has no projection of that name. The read
  `Alias.field` is then an unknown constant at the Lean build, which is
  loud (measured above).

## 3. Tests

**Case file.** `tests/comprehensive/test_instance_reader.lem` covers:

- simple lifting;
- transitive lifting;
- a non-lifted control;
- a bare reference;
- `Let_def` values (a single name and a destructuring pair);
- a multi-clause group;
- two instance readers (binders `[Md] [Sw]`);
- a consumer, including a higher-order reference;
- a consumer that is an explicit-reader, instance-reader and fuel
  consumer at once;
- seed definitions, with and without instance reach;
- a structural mutual pair and a fuel'd mutual pair;
- coexistence of an explicit reader, the instance reader and fuel;
- a measured definition;
- a supply-lifted definition.

Two `.lem` asserts check that the unbound definitions stay unbound.

**Lean files.**

- `lean-test/TestInstanceReaderImpl.lean`: the hand-written classes `Sw`
  and `Md` and the consumer implementations. It declares no instance.
- `lean-test/TestInstanceReaderCheck.lean`:
  - SIGNATURE pins: every lifted definition's type is ascribed with its
    exact binder kinds and order, e.g.
    `example : [Md] → [Sw] → Nat → Nat := @both_readers`;
  - the `_zero` lemmas and the obligation are applied under `[Sw]`;
  - KERNEL `rfl` pins at concrete instances, e.g.
    `@calls_get_sw ⟨5⟩ = fun x => (5 + x) * 2`, the `letI` form,
    `@mixed ⟨2⟩ ⟨5⟩ 2 4 = 999` (insufficient fuel) and
    `@rping_lemFuel ⟨7⟩ 3 3 = 992`;
  - two quantified theorems that bind the instance.
- `lean-test/Test_instance_reader_lemMeasureProofs.lean`: proves the
  measured obligation with kernel-only tactics. The build log, verbatim:
  `'Test_instance_reader_lemMeasureProofs.ilen_measure_sufficient' depends on axioms: [propext, Quot.sound]`.
- `lean-test/TestInstanceReaderExec.lean`, suite phase
  `lean-instance-reader`: a compiled binary.
  - Its instance is chosen at RUNTIME from the argument count, and the
    phase runs it with zero and with one argument.
  - It re-asserts the transitive callee, the consumer, the seed
    definition, the triple consumer, the fuel'd mutual pair, the
    coexistence definition and the measured definition.
  - Vacuity plant: the expectation for `get_sw` was changed to `v + 4`.
    The binary printed `FAIL: get_sw: got 8, want 9` and exited 1;
    reverted, it printed `instance reader: OK`.

**Probes and invariance.**

- `negative/neg_ireader_*.lem`: 19 probes, one or more per fail-closed
  rule (§4 lists the plants). The review round added four:
  `neg_ireader_body` (IR-body), `neg_ireader_inline` (IR-inline),
  `neg_ireader_poly` (IR-type, polymorphic) and `neg_ireader_class_alias`
  (IR-class, last component).
- **No-instance gate** (review F6, phase `lean-no-ireader-instances`,
  `tests/comprehensive/check_no_ireader_instances.sh`). It derives the
  instance-reader classes from every `reader val … = instance` declaration
  in the repository's `.lem` files, then scans every `.lean` file under
  `tests/` and `lean-lib/` (`.lake/` excluded, comments stripped). It
  fails on an `instance … : C`, an `@[instance]` definition of type `C`,
  a `deriving instance … C … for`, or any `attribute [instance]` line.
  It is vacuity-guarded: at least one class must be derived, at least 100
  files scanned, and some scanned file must define a derived class. The
  plants are in §4.
- `invariance/inv_instance_reader.lem`: the two `{lean}` declarations are
  exact no-ops for OCaml, HOL, Isabelle and Coq.

**Suite tail** (`make -C tests/comprehensive lean`, review round, run
on the final source; the binary is §5's `new` binary). The lines are
verbatim; the bracketed notes are derived counts:

```
=== Generation: 74 passed, 0 failed, 0 skipped ===
Build completed successfully (213 jobs).
  OK: compiled instance-reader lifting holds at two runtime instances
  OK (rejected as declared): negative/neg_ireader_body.lem
  OK (rejected as declared): negative/neg_ireader_class_alias.lem
  OK (rejected as declared): negative/neg_ireader_class_dup.lem
  OK (rejected as declared): negative/neg_ireader_inline.lem
  OK (rejected as declared): negative/neg_ireader_poly.lem
      [these 5 shown; all 19 neg_ireader_* probes print this line; 134 probes rejected as declared in all]
  OK: inv_instance_reader.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
  OK: 12 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
  OK: 535 Lean files scanned; no instance of the 5 instance-reader classes (NegImpl.Sw, NegImpl.Sw2, Sw, TestInstanceReaderImpl.Md, TestInstanceReaderImpl.Sw)
  OK: 328 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
rc=0
/home/dev/projects/cerberus-lean-proj/scripts/ce make -C tests/comprehensive   425.89s user 29.23s system 95% cpu 7:57.71 total
```

The S0 run's suite tail was the same apart from the probe count (15
`neg_ireader_*`, 130 in all) and the new gate line; it was rc=0 in
8m40.770s.

**Other gates, verbatim (review round).**

- LemLib (`cd lean-lib && <container>/cerberus-lean/scripts/capped lake build`):
  `Build completed successfully (39 jobs).`
- `make nonlean-regress`:
  `nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)`.
  The goldens did not move. The corpus (library and `tests/backends`)
  uses neither declaration form, so the F4 printer fix cannot reach it.

## 4. Plants (the guards are load-bearing)

**Method.** `.tmp/plants.py` (scratch, deleted with `.tmp/`) worked
through the guards one at a time. For each guard it:

1. disabled that one guard in the source;
2. rebuilt `lem`;
3. ran every `neg_ireader_*` probe;
4. restored the file from a byte copy and checked it by SHA-256.

**Results.** Verbatim:

```
baseline: all 15 neg_ireader probes rejected as declared
P1 scope net off (ireader_scope_check is a no-op): 5 probe(s) turned red
    neg_ireader_consumer_scope.lem: ACCEPTED
    neg_ireader_indreln.lem: ACCEPTED
    neg_ireader_instance_method.lem: ACCEPTED
    neg_ireader_scope_assert.lem: ACCEPTED
    neg_ireader_scope_direct.lem: ACCEPTED
    restored src/lean_backend.ml (sha256 verified)
P2 IR-proj off (any projection text accepted; class = text): 2 probe(s) turned red
    neg_ireader_proj.lem: ACCEPTED
    neg_ireader_proj_root.lem: ACCEPTED
    restored src/lean_backend.ml (sha256 verified)
P3 IR-mix off: 2 probe(s) turned red
    neg_ireader_fuel_mix.lem: ACCEPTED
    neg_ireader_mix.lem: ACCEPTED
    restored src/lean_backend.ml (sha256 verified)
P4 IR-type off: 1 probe(s) turned red
    neg_ireader_type.lem: ACCEPTED
    restored src/lean_backend.ml (sha256 verified)
P5 IR-class off: 1 probe(s) turned red
    neg_ireader_class_dup.lem: ACCEPTED
    restored src/lean_backend.ml (sha256 verified)
P6 redeclaration check off (typecheck): 1 probe(s) turned red
    neg_ireader_twice.lem: ACCEPTED
    restored src/typecheck.ml (sha256 verified)
P7 IRC-reader off: 1 probe(s) turned red
    neg_ireader_consumer_notreader.lem: ACCEPTED
    restored src/lean_backend.ml (sha256 verified)
P8 IRC-rep off: 1 probe(s) turned red
    neg_ireader_consumer_norep.lem: ACCEPTED
    restored src/lean_backend.ml (sha256 verified)
P9 IRC-mix off: 1 probe(s) turned red
    neg_ireader_consumer_mix.lem: ACCEPTED
    restored src/lean_backend.ml (sha256 verified)
```

**Reading.**

- Each guard is the only thing standing between its probe and silent
  acceptance.
- Each plant flips exactly its own probes; no probe is rejected for
  another guard's reason.
- P3's `neg_ireader_mix` is accepted without IR-mix: an explicit and an
  instance reader on one val would then both apply.

**Rebuild after revert.** After the plants, the source hashes matched
the pre-plant hashes:

```
src/lean_backend.ml: OK
src/typecheck.ml: OK
```

The rebuilt binary was byte-identical to the binary that produced the
invariance witness (§5):

```
7cf258ca32ba288ceccf687219961bc5014e7be2467667ea6cf7326a17590aac  src/main.native
7cf258ca32ba288ceccf687219961bc5014e7be2467667ea6cf7326a17590aac  .tmp/lem-final
```

### Review-round plants (2026-10-05)

The same method (`.tmp/plants2.py`, scratch) was used for the guards the
review round added, and for IR-class's new comparison. Verbatim:

```
baseline: all 19 neg_ireader probes rejected as declared
P10 IR-body off: 1 probe(s) turned red
    neg_ireader_body.lem: ACCEPTED
    restored src/lean_backend.ml (sha256 verified)
P11 IR-inline off: 1 probe(s) turned red
    neg_ireader_inline.lem: ACCEPTED
    restored src/lean_backend.ml (sha256 verified)
P12 IR-type polymorphism off: 1 probe(s) turned red
    neg_ireader_poly.lem: ACCEPTED
    restored src/lean_backend.ml (sha256 verified)
P13 IR-class last-component comparison off (whole-text equality, as before F3): 1 probe(s) turned red
    neg_ireader_class_alias.lem: ACCEPTED
    restored src/lean_backend.ml (sha256 verified)
P5 IR-class off entirely: 2 probe(s) turned red
    neg_ireader_class_alias.lem: ACCEPTED
    neg_ireader_class_dup.lem: ACCEPTED
    restored src/lean_backend.ml (sha256 verified)
after revert + rebuild: all probes rejected as declared
```

The rebuilt binary after the revert was
`569ff23e799b8d50bcaf13df1a964f0e256b7379bcff65a3c9728d71cdebb68f`, the
binary of the suite run (§3) and of §5's `new` side.

**No-instance gate plants (F6).** Each line was appended to
`lean-test/TestInstanceReaderCheck.lean`, the gate was run, and then the
file was restored from a byte copy. Verbatim (the `==` headers and the
`rc=` lines are printed by the plant loop):

```
== P-I1a: instance : Sw := ⟨5⟩
  FAIL: an instance of an instance-reader class (a hidden default):
  I1 /home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-arc/pnvi-switches/tests/comprehensive/lean-test/TestInstanceReaderCheck.lean:94: instance : Sw := ⟨5⟩
rc=1
== P-I1b: instance (priority := low) swInst : TestInstanceReaderImpl.Sw where sw := 5
  FAIL: an instance of an instance-reader class (a hidden default):
  I1 /home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-arc/pnvi-switches/tests/comprehensive/lean-test/TestInstanceReaderCheck.lean:94: instance (priority := low) swInst : TestInstanceReaderImpl.Sw where sw := 5
rc=1
== P-I1c: scoped instance foo {n : Nat} : _root_.TestInstanceReaderImpl.Md := ⟨true⟩
  FAIL: an instance of an instance-reader class (a hidden default):
  I1 /home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-arc/pnvi-switches/tests/comprehensive/lean-test/TestInstanceReaderCheck.lean:94: scoped instance foo {n : Nat} : _root_.TestInstanceReaderImpl.Md := ⟨true⟩
rc=1
== P-I2: @[instance] def swDef : Sw := ⟨5⟩
  FAIL: an instance of an instance-reader class (a hidden default):
  I2 /home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-arc/pnvi-switches/tests/comprehensive/lean-test/TestInstanceReaderCheck.lean:94: @[instance] def swDef : Sw := ⟨5⟩
rc=1
== P-I3: deriving instance Sw for Nat
  FAIL: an instance of an instance-reader class (a hidden default):
  I3 /home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-arc/pnvi-switches/tests/comprehensive/lean-test/TestInstanceReaderCheck.lean:94: deriving instance Sw for Nat
rc=1
== P-I4: attribute [instance] swDef
  FAIL: an instance of an instance-reader class (a hidden default):
  I4 /home/dev/projects/cerberus-lean-proj/worktrees/lem-lean-arc/pnvi-switches/tests/comprehensive/lean-test/TestInstanceReaderCheck.lean:94: attribute [instance] swDef
rc=1
== N-ctl1: instance : Inhabited Nat := ⟨0⟩
  OK: 535 Lean files scanned; no instance of the 5 instance-reader classes (NegImpl.Sw, NegImpl.Sw2, Sw, TestInstanceReaderImpl.Md, TestInstanceReaderImpl.Sw)
rc=0
== N-ctl2: example : (letI : Sw := ⟨5⟩; calls_get_sw 3) = 16 := rfl
  OK: 535 Lean files scanned; no instance of the 5 instance-reader classes (NegImpl.Sw, NegImpl.Sw2, Sw, TestInstanceReaderImpl.Md, TestInstanceReaderImpl.Sw)
rc=0
== N-ctl3: -- instance : Sw := ⟨5⟩
  OK: 535 Lean files scanned; no instance of the 5 instance-reader classes (NegImpl.Sw, NegImpl.Sw2, Sw, TestInstanceReaderImpl.Md, TestInstanceReaderImpl.Sw)
rc=0
restored lean-test/TestInstanceReaderCheck.lean (sha256 verified)
  OK: 535 Lean files scanned; no instance of the 5 instance-reader classes (NegImpl.Sw, NegImpl.Sw2, Sw, TestInstanceReaderImpl.Md, TestInstanceReaderImpl.Sw)
rc=0
```

The vacuity guards were run on a scratch copy of the script under a
synthetic root. With no `.lem` declaration it printed
`FAIL (vacuous): no instance-reader declaration found in the .lem files`.
With declarations but no Lean files it printed
`FAIL (vacuous): only 0 Lean files to scan (< 100)`. With 120 files but
no class definition it printed
`FAIL (vacuous): no scanned file defines a derived class (TestInstanceReaderImpl.Md, TestInstanceReaderImpl.Sw)`.
After adding `class Sw` it printed
`OK: 120 Lean files scanned; no instance of the 2 instance-reader classes (TestInstanceReaderImpl.Md, TestInstanceReaderImpl.Sw)`.

## 5. Invariance witness: S0 is a pure addition

### Claim

For inputs that use neither declaration form, the new backend's output
is BYTE-IDENTICAL to `4e70bb5`'s. This holds for Lean and for OCaml.

### Method

The script `.tmp/gen_all.sh` (scratch) generated the outputs listed in
the table below twice, into separate scratch directories:

- **Baseline:** the PINNED lem, i.e. the opam `lem` in the shared switch,
  `Lem lean-backend-v0.1.0-alpha.1-63-g4e70bb5` (`4e70bb5`).
- **New:** the branch's in-tree `lem` (root `make`), run from a frozen
  copy of the binary and of the script.

Both runs used the same `LEMLIB`, the pinned switch's `share/lem/library`
(its `.lem` files are identical to the worktree's). Inputs that use the
new forms were excluded from the second run, because the claim is about
inputs that do not use them. Those are `test_instance_reader.lem` and the
`neg_ireader_*` probes; neither existed when the baseline ran.

**Cerberus input.** The Cerberus sources were read, read-only, from the
primary checkout at mainline `1806c5a23`, which is `1001f3f2b` plus the
asm-refusal merge. The primary checkout moved from `1001f3f2b` to
`1806c5a23` at 06:31:02, before the baseline generated Cerberus (06:33).
No `.lem` file was newer than the baseline output when the final run
finished, and the reflog shows no later move. So both runs read the same
sources.

The Cerberus invocations are exactly those of `make lean-prelude-src`
(`-cerberus_pp -lean`, `LEM_SRC_LEAN`) and of the `prelude-src` OCaml
rule (`-cerberus_pp -ocaml`, `LEM_SRC`). The source lists were taken from
the Makefile with `make --eval`.

### What was compared

| Output set | Files | What it is |
|---|---|---|
| `cerb-lean` | 170 | the full Cerberus Lean generated tree |
| `cerb-ocaml` | 86 | the Cerberus OCaml tree |
| `lib-lean` | 58 | LemLib's generated modules (the `lean-libs` invocation) |
| `lib-ocaml` | 29 | the library's OCaml (the `ocaml-libs` invocation) |
| `comp-lean` | 146 | every `tests/comprehensive/test_*.lem`, Lean |
| `comp-ocaml` | 113 | the same, OCaml; Lean-only tests refused identically on both sides |
| `comp-lean-joint1`, `comp-lean-joint2` | 4 + 4 | the two joint pairs |
| `comp-neg` | 115 | every negative probe's refusal text |
| `parity-lean`, `parity-ocaml` | 98 + 49 | the parity probes |
| `backends-lean`, `backends-ocaml` | 24 + 13 | `tests/backends`, Lean and OCaml |
| logs | 10 | every log and refusal list |

### Result, verbatim

```
$ diff -r base-opam new-final > diff-final.txt; echo "diff -r exit: $?"; wc -l < diff-final.txt
diff -r exit: 0
0
cerb-lean           170 files: identical
cerb-ocaml           86 files: identical
lib-lean             58 files: identical
lib-ocaml            29 files: identical
comp-lean           146 files: identical
comp-ocaml          113 files: identical
comp-lean-joint1      4 files: identical
comp-lean-joint2      4 files: identical
comp-neg            115 files: identical
parity-lean          98 files: identical
parity-ocaml         49 files: identical
backends-lean        24 files: identical
backends-ocaml       13 files: identical
backends.log identical
backends-refusals.txt identical
cerb-lean.log identical
cerb-ocaml.log identical
comp-lean.log identical
comp-ocaml.log identical
comp-ocaml-refusals.txt identical
lib-lean.log identical
lib-ocaml.log identical
parity.log identical
```

(The table lines are derived per directory from the same two trees.)

### Re-run after the review round (2026-10-05)

The witness was re-run with the same method, from re-written scratch
(`.tmp/gen_all.sh`; the S0 copy had been deleted with `.tmp/`).

- **Baseline:** the opam `lem` of the shared switch, copied to scratch:
  `Lem lean-backend-v0.1.0-alpha.1-63-g4e70bb5`.
- **New:** the review-round binary, frozen
  (`569ff23e…`; `Lem lean-backend-v0.1.0-alpha.1-64-gfc8fbef-dirty`;
  "dirty" because it was built from the then-uncommitted final source,
  which is this commit's source).
- **Inputs.** `LEMLIB` was the pinned switch's `share/lem/library`.
  Cerberus was read at the primary checkout `1806c5a23` (HEAD checked
  before and after; unchanged). The Cerberus source lists came from
  `make --eval` (85 Lean and 86 OCaml sources).
- **Exclusions.** The new-form inputs were excluded on both sides:
  `test_instance_reader.lem` and every `neg_ireader_*` probe.
- **Layout change.** `comp-ocaml` now also holds one captured-output file
  per test (73 of its 186 files), and each joint directory holds its log,
  so those counts differ from the S0 table.

Verbatim:

```
diff -r exit: 0
0
cerb-lean            170 files: identical
cerb-ocaml            86 files: identical
lib-lean              58 files: identical
lib-ocaml             29 files: identical
comp-lean            146 files: identical
comp-ocaml           186 files: identical
comp-lean-joint1       5 files: identical
comp-lean-joint2       5 files: identical
comp-neg             115 files: identical
parity-lean           98 files: identical
parity-ocaml          49 files: identical
backends-lean         24 files: identical
backends-ocaml        13 files: identical
backends.log identical
backends-refusals.txt identical
cerb-lean.log identical
cerb-ocaml.log identical
comp-lean.log identical
comp-ocaml.log identical
comp-ocaml-refusals.txt identical
lib-lean.log identical
lib-ocaml.log identical
parity.log identical
```

### Cross-check against a checked-in tree

**The scratch regeneration matches a real tree.** It was compared with
the generated tree of the asm-refusal worktree (`5643929bb`, the content
of mainline `1806c5a23`). 169 of 170 files are byte-identical. The one
exception is `Core_run.lean`, which is identical after the Makefile's
`sed '/^import Operators$/d'`.

**The primary checkout's own tree is stale.** The primary checkout's
`lean_frontend/generated/` differs in all 170 files. It predates the
`4e70bb5` layout re-pin and does not reflect its sources. This is a
finding about that checkout, not about S0, and is noted for the
orchestrator.

### What the other gates add

- The suite phase `lean-invariance` checks that the new `{lean}`
  declarations are no-ops for the other emitters:
  `OK: inv_instance_reader.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)`.
- `nonlean-regress` re-checks the nine non-Lean emitters against their
  goldens.

## 6. Limitations

- **Inductive relations are not lifted by this mechanism.** The fuel
  lifting does lift them (it takes `[LemFuel]` as an inductive
  parameter); the instance reader does not. A rule that reaches an
  instance reader is the loud scope error (`neg_ireader_indreln`).
  Extend the mechanism if Cerberus needs it. Whether any Cerberus switch
  read is reachable from an indreln has not been measured; S1's
  generation will show it, loudly, if one is.
- **Instance readers are not seedable.** A seed definition binds the
  class; it cannot supply a value. A different value is supplied by the
  caller (`@f ⟨v⟩`, `letI`), lexically, as Lean's instances are.
- **Positional instance arguments are sensitive to reader names**
  (review F7). The binder order follows the lem reader NAME, not the
  class. `@f ⟨n⟩ ⟨v⟩` depends on that order. Renaming an instance reader
  can reorder binders, which is the explicit readers' caveat. Distinct
  classes make a swap a type error unless the field types coincide.
  - A definition binds only the readers it reaches. So a definition that
    reaches ONE reader keeps its positional signature when a second
    reader is added elsewhere.
  - A definition that comes to reach a second reader gains a binder, and
    where the new reader's name sorts first, the new binder comes first.
    So adding a second instance reader in a downstream project changes
    the signature of every definition reaching both. That is a signature
    change for consumers that apply them explicitly (`@f ⟨…⟩ ⟨…⟩`).
  - Consumers should therefore prefer `letI : Cls := ⟨v⟩` (or named
    instance arguments) over positional `@f ⟨…⟩` wherever two readers
    meet. `letI` is order-independent.
- **Kernel computation needs a non-`partial` definition** (review F5,
  advisory for downstream). Binding `[Cls]` does not change how a
  definition is compiled. A `partial def` that binds `[Cls]` runs, at
  any instance, but it is opaque to the kernel. So a fact proved by
  `rfl` or `decide` at a concrete instance (`@f ⟨v⟩ x = y`) holds only
  where `f` and everything it unfolds to are fuel'd (`[LemFuel]`, a
  closed fuel at the entry point) or structural. A consumer planning
  `rfl`-level facts at a concrete switch setting must check that the
  definitions under it are not `partial`; the instance mechanism does
  not make an opaque definition computable.
- **Explicit readers keep two pre-existing gaps** (found with review F1;
  TODO #52). An explicit `declare {lean} reader val cfg` with a lem body
  and no Lean target_rep is emitted as a dead
  `def cfg (_lemReader_cfg : Nat) (u : Unit) : Nat := 0`. With
  `let inline cfg u = 0`, a read is silently inlined, giving
  `def g (x : Nat) : Nat := 0 + x`, with no reader binder. Both were
  reproduced on the S0 branch. The instance form refuses both shapes
  (IR-body, IR-inline). The explicit form is deliberately unchanged in
  this slice, because changing it would break the S0 invariance witness
  (§5). Cerberus's two explicit readers (`tagDefs`, `enum_definitions`)
  both carry a non-inline Lean target_rep at `1806c5a23`, by reading, so
  Cerberus is not affected today.
- **Class shape is Lean's check.** The class's existence and the field's
  type are checked by Lean at build time ("unknown constant", a type
  mismatch at the read site), not at generation. Both are loud.
- **The import heuristic is syntactic.** The class's module is imported
  only when its first dotted component is a module name (the target_rep
  heuristic). Otherwise `declare {lean} extra_import` is needed, and its
  absence is a loud Lean error.
- **Pre-existing refusals stand.** Supply lifting in a truly mutual block
  and `reader_seed` in a mutual block were refused before S0 and still
  are. S0 lifts no refusal.

## 7. Deviations from the design record's §B.3

These are all [AGENT] decisions, recorded for review.

1. **Syntax.** The form is ``reader val r = instance `Cls.field` ``,
   which names the projection. §B.3's example
   ``reader_binder switches = instance `CerbGlobal.Switches` `` names the
   class. Reason: §2 "Why this syntax"; the payload sits on `reader val`,
   which is what §B.3 calls "a flag on `reader val`".
2. **Consumer.** The consumer role is
   `reader_consumer val f = instance r`, naming its reader. §B.3's
   working name was `switches_consumer`. It is per-reader rather than for
   all readers.
3. **Class import.** The class's module is imported automatically by the
   target_rep heuristic. §B.3 does not mention imports.
4. **Pin dance not done.** §E row S0 lists "the two-repo pin dance" in
   the slice. Per this slice's brief it is not done here: no opam pin,
   Lake rev, manifest or `fork_drift_manifest.txt` change. The
   orchestrator does it after review.

## 8. Adversarial review: findings and dispositions (2026-10-05)

The adversarial review of `fc8fbef` found no soundness defects. The
orchestrator's brief for this round set the dispositions below, and the
operator approved the round on 2026-10-05 (as relayed by the brief).
Where the worker departed from the brief, the entry is marked [AGENT].

| # | Finding | Disposition |
|---|---------|-------------|
| F1 | An instance reader with a lem body and no Lean target_rep emitted a dead `def sw [Impl.Sw] (u : Unit) : Nat := 0`. | **Refused** (IR-body, in the pre-pass at the definition; probe `neg_ireader_body`). The brief preferred refusal to suppressing the def, and so did the worker [AGENT]. Suppressing it would leave a lem-defined constant with no Lean counterpart, which is silent for hand-written callers; refusing says so at generation. While reproducing F1, a worse variant was found: `let inline sw u = 0` is inlined before emission, so reads silently become `0` and the reading def binds no class. That is **refused** too (IR-inline, `neg_ireader_inline`) [AGENT]. The same two gaps exist for explicit readers; per the brief they are **not changed** here (they would break the invariance witness), but are recorded in §6 and as TODO #52. |
| F2 | IR-type accepted `val sw : forall 'a. unit -> 'a`. | **Refused**: free type variables in the reader's type (IR-type; `neg_ireader_poly`). |
| F3 | IR-class compares class texts syntactically. | **Documented** (§2, DESIGN.md) as the brief asked, and **tightened** [AGENT]. The brief's premise that "Lean then fails loudly" was measured. It holds for the review's `_private.` example, but not for a namespace-relative or `open`ed alias: two binders of one class are legal Lean and the reads silently conflate (§2, "IR-class and name resolution"). IR-class now compares last components (`neg_ireader_class_alias`). This goes beyond the brief and is flagged for review; reverting it is one line plus the probe. |
| F4 | A double space in the human-target printers. | **Fixed.** The parser's skip before the backticked payload is now carried in the typed AST (`Decl_reader_instance` holds `lskips * string`) and printed, instead of a hard-coded leading space. html now prints ``<b>instance</b> `Impl.Sw.sw` ``, tex prints `\lemkw{instance}\  ` followed by the payload, and `-lem` round-trips the source line exactly. The `nonlean-regress` goldens did not move. |
| F5 | `partial def` with `[Cls]` is kernel-opaque. | **Documented** (§6, advisory for downstream). |
| F6 | Nothing stopped an instance of a reader class appearing in lem-lean's Lean tree. | **Gate added**: `check_no_ireader_instances.sh`, phase `lean-no-ireader-instances` in `make -C tests/comprehensive lean`. The classes are derived from the `.lem` declarations, the gate is vacuity-guarded, and it was plant-tested (§3, §4). |
| F7 | The binder order follows the reader name, so positional application is fragile. | **Documented** (§6, DESIGN.md, manual). |

## 9. Delta audit A-1, A-2, A-2b (2026-10-08, branch `docs/ireader-a1-a2`)

A delta audit of this mechanism made three findings. This slice changes
docs and a test gate only. `src/` is untouched, so `lem -v` still matches
the pin `2d3a492`.

| # | Finding | Disposition |
|---|---------|-------------|
| A-1 | DESIGN.md gave `_private.Impl.Sw` and an `export` alias as texts whose last component differs from `Impl.Sw`. Both end in `Sw`, so the tightened IR-class check refuses them at generation. Only the `abbrev` example was right. | **Fixed** in DESIGN.md ("IR-class is syntactic"). §2 above gets a dated note: its `export`/`_private.` measurements predate the tightening. The manual (`doc/manual/backend_lean.md`) states the rule without examples and was already correct. |
| A-2 | The F6 gate missed `instance : (Sw)`, a header split across lines, and `abbrev SwA := Sw` followed by `instance : SwA`. | The gate is a speedbump, not a trust surface ([USER 2026-10-07]: a classic case of gate cruft — gates are not to be adversarially robust unless they are trust surfaces). **The parenthesised class is closed** [AGENT]: I1 and I2 now accept one optional `(` before the class, a one-token regex change. **Split headers and aliases are out of scope by design**, and the script header now says so. No alias tracking was added. |
| A-2b | The IR-body message suggests "drop the lem definition", but a bare `val` that is then read fails to typecheck. | **Measured**: a bare `val sw`, declared as an instance reader and read, gives `Type error: unbound variable for targets {lean}: sw`. The message is in `src/`, so this slice does not change it. Recorded as TODO #53. |

**Plants (A-2).** Method: append the line to
`lean-test/TestInstanceReaderCheck.lean`, run the gate, then restore the
file from a byte copy. Afterwards `cmp` confirmed the restore and
sha256 was `eb9b7795…a65531e`. The tree was generated by
`make -C tests/comprehensive lean` (535 files scanned). The
`rc=` lines were printed by the plant loop. Verbatim:

```
rc=1 :: instance : (Sw) := ⟨5⟩ 
rc=1 :: instance swP : ( TestInstanceReaderImpl.Sw ) where sw := 5 
rc=1 :: @[instance] def swDefP : (Sw) := ⟨5⟩ 
rc=1 :: instance : Sw := ⟨5⟩ 
rc=1 :: instance (priority := low) swInst : TestInstanceReaderImpl.Sw where sw := 5 
rc=1 :: scoped instance foo {n : Nat} : _root_.TestInstanceReaderImpl.Md := ⟨true⟩ 
rc=1 :: @[instance] def swDef : Sw := ⟨5⟩ 
rc=1 :: deriving instance Sw for Nat 
rc=1 :: attribute [instance] swDef 
rc=0 :: instance : (Inhabited Nat) := ⟨0⟩ 
rc=0 :: example : (letI : Sw := ⟨5⟩; calls_get_sw 3) = 16 := rfl 
rc=0 :: abbrev SwA := Sw instance : SwA := ⟨5⟩ 
rc=0 :: instance :   Sw := ⟨5⟩ 
```

The first three lines are the new parenthesised plants. The next six
re-run the §4 plants (P-I1a through P-I4). `(Inhabited Nat)` and the
`letI` line are controls that must stay green. The last two lines are
the alias and split-header shapes. They stay green, which is the
documented scope, not a defect. As a load-bearing check, the gate as it
was at `2d3a492` passed `instance : (Sw) := ⟨5⟩`:
`OK: 535 Lean files scanned; no instance of the 5 instance-reader classes (NegImpl.Sw, NegImpl.Sw2, Sw, TestInstanceReaderImpl.Md, TestInstanceReaderImpl.Sw)`,
`old gate rc=0`.
