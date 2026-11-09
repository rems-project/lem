# The `[Eq0 a] : BEq a` bridge and core `BEq`: design note (2026-10-03)

Status: a DESIGN PASS for the operator to rule on. No code is changed by this
note. Branch `docs/beq-lattice-design`, from `mdd/lean-backend` at `5dfcd25`.

Ruling that commissioned it, as relayed by the orchestrator: operator ruling
[USER 2026-10-03], #2: design pass first. Background: codereview finding L1
(container-local `.tmp/codereview/REPORT.md` §6 L1, F-I1 in
`notes-lemlib.md`), the lattice note
`doc/notes/2026-08-22_arc14-instance-priority-lattice.md`, and DESIGN.md
"Instance priorities come from one table".

All judgements, options and recommendations here are [AGENT] unless marked
otherwise. Every Lean run went through `cerberus-lean/scripts/capped` against
LemLib built at `5dfcd25` in a scratch detached worktree, which has since been
removed. The probe files are quoted inline where they matter. Tallies marked
"derived" are sums of measured rows, not separate measurements.

## 1. Summary

- [AGENT] **Recommendation: option (a), with two priority changes.** Put the
  `[Eq0 a] : BEq a` bridge at **450**, and both comparator bridges
  (`[SetType a]`, `[MapKeyType a]`) at **400**. All three then sit below core's
  `instBEqOfDecidableEq`, which is at **500** in Lean 4.32.2, not at the
  default 1000. As a side effect, LemLib's own base `Eq0` instances elaborate
  through core, so option (c) comes with it for free.
- **Values do not change.**
  - Old `==` equals new `==` at every base type: there is a kernel theorem per
    type (§4).
  - Every switched instance in both consumers is value-equal (§5).
  - The generated text of the consumers is byte-identical. Only three
    priority lines of LemLib text change, across two files.
- **What changes.** Elaborated `==` terms move in about 900 cerberus and about
  740 linksem generated declarations (derived counts).
- **Who must re-prove.** Hand-written proofs that spell out the bridge: 2 in
  cerberus-lean and 9 in cerberus-sl. All become one-liners. linksem has none.

## 2. The lattice as it is (measured at `5dfcd25`)

### 2.1 Priorities

The table below lists every `BEq`, `Eq0`, `Ord0` and `Inhabited` instance
that LemLib declares. It was dumped from `instanceExtension` with
`import LemLib.Pervasives_extra` and `import LemLib.Bridges`, and abridged to
LemLib plus the relevant core rows:

| Class | Priority | Instance | Where | Why it exists |
|---|---|---|---|---|
| BEq | 1000 | `Lem_Basic_classes.instBEqOfEq0` (star `[Eq0 a] : BEq a`) | Basic_classes:32, emitted at `src/lean_backend.ml:4634-4639` | Lem's `isEqual` has target rep `infix ==` (basic_classes.lem:28), so `==` must work wherever an `Eq0` dictionary exists (polymorphic `[Eq0 a]` code) |
| BEq | 500 | `Lem_Basic_classes.instBEqOfSetType` (star) | Basic_classes:184, `lean_backend.ml:4641-4654` | `==` from a comparator; arc-14 R3 de-tie |
| BEq | 500 | `Lem_Map.instBEqOfMapKeyType` (star) | Map:55 | the same, for `MapKeyType` |
| BEq | **500** | **core `instBEqOfDecidableEq`** (star) | `Init/Prelude.lean:1077` `instance (priority := 500) [DecidableEq α] : BEq α` | core: the BEq of Nat/Int/String/Char/Bool/Unit/UIntN/IntN/BitVec |
| BEq | 1000 | `instBEqPset`, `instBEqFmap`, `instBEqSum_lemLib`, `instBEqLemOrdering`, `instBEqLemRational/Real/Float*` (specific) | LemLib.lean | structural `deriving BEq` support; panic stubs for unsupported numerics |
| BEq | 1000 | `Lem_Word.instBEqBitSequence` | Word | derived |
| Eq0 | 1000 | `instEq0Nat`, `instEq0Nat_1` (num.lem declares `Eq nat` twice: natural and nat), `instEq0Int`, `instEq0Int_1`, `instEq0Int32`, `instEq0Int64`, `instEq0String`, `instEq0Char`, `instEq0Bool`, `instEq0LemOrdering`, `instEq0Unit` (Bridges), and the compound ones (Prod ×5, List, Option, Sum, Pset, Fmap, BitVec, bitSequence_1) | Num, Basic_classes, … | Lem class dictionaries (`instance (Eq nat)` …) |
| Eq0 | 500 | `Lem_Word.instEq0BitSequence` | Word | the backend's auto trio |
| Eq0 | 100 | `instEq0OfBEq` (`[BEq a] : Eq0 a`) | Basic_classes:64 | Lem's `default_instance` (unsafe structural equality) |
| Ord0 | 1000 / 500 | base types, compound types / auto-trio `bitSequence` | Num, List, … | Lem dictionaries |
| SetType | 100 | `instSetTypeOfOrd` (`[Ord a] : SetType a`) | Basic_classes:190 | generic default |
| OrdMaxMin | 100 | `instOrdMaxMinOfOrd0` | Basic_classes:161 | generic default |
| Inhabited | 1000 / 100 | `Sum` left / right, `Pset`, `Pmap`, `Fmap`, `LemOrdering`, stubs | LemLib.lean | `Inhabited` for derivation |

Measured fact, missing from the lattice note: **core's `instBEqOfDecidableEq`
is at 500, not 1000.** As a result:

1. The `Eq0` bridge (1000) beats core by **priority** at every base type.
2. The comparator bridges (500, star) **tie** with core (500, star). The tie is
   decided by declaration order, and LemLib's bridges are newer, so they win.
   This tie is not listed in the lattice note's "deliberate ties", and that
   note says "adding a new tie is a finding". [AGENT] This is a second finding
   beside L1.

### 2.2 What resolution picks today

`#synth` output, verbatim (with `set_option pp.explicit true`):

```
@instBEqOfEq0 Nat Lem_Num.instEq0Nat_1
@instBEqOfEq0 Int Lem_Num.instEq0Int_1
@instBEqOfEq0 String instEq0String
@instBEqOfEq0 Char instEq0Char
@instBEqOfEq0 Bool instEq0Bool
@Lem_Map.instBEqOfMapKeyType Unit (@Lem_Map.instMapKeyTypeOfSetType Unit (@instSetTypeOfOrd Unit instOrdUnit_lemLib))   [without Bridges imported]
@List.instBEq Nat (@instBEqOfEq0 Nat Lem_Num.instEq0Nat_1)
@Option.instBEq Nat (@instBEqOfEq0 Nat Lem_Num.instEq0Nat_1)
@instBEqProd Nat Nat (@instBEqOfEq0 Nat Lem_Num.instEq0Nat_1) (@instBEqOfEq0 Nat Lem_Num.instEq0Nat_1)
@instBEqPset Nat (@instBEqOfEq0 Nat Lem_Num.instEq0Nat_1)
@instBEqOfEq0 Int64 Lem_Num.instEq0Int64
@Lem_Map.instBEqOfMapKeyType (BitVec 8) (… (@instSetTypeOfOrd (BitVec 8) (@instOrdBitVec 8)))
Probe/P1.lean:16:0: error: failed to synthesize
  @LawfulBEq Nat (@instBEqOfEq0 Nat Lem_Num.instEq0Nat_1)
```

Without LemLib, the same `#synth` gives `@instBEqOfDecidableEq Nat
instDecidableEqNat` and `Nat.instLawfulBEq`.

The bridge at a base type is **three instances deep**. `#print`, verbatim:

```
def Lem_Num.instEq0Nat_1 : Eq0 Nat :=
@Eq0.mk Nat (fun x y => @BEq.beq Nat (@instBEqOfEq0 Nat Lem_Num.instEq0Nat) x y) …
def Lem_Num.instEq0Nat : Eq0 Nat :=
@Eq0.mk Nat (fun x y => @BEq.beq Nat (@instBEqOfSetType Nat (@instSetTypeOfOrd Nat instOrdNat)) x y) …
def Lem_Basic_classes.instEq0String : Eq0 String :=
@Eq0.mk String (fun x y => @BEq.beq String (@instBEqOfSetType String (@instSetTypeOfOrd String String.instOrd)) x y) …
```

So `a == b` at `Nat` currently means `match defaultCompare a b with | .EQ =>
true | _ => false`, computed through `Ord Nat`. Where each base body comes
from:

- `instEq0Nat`, `instEq0Int`, `instEq0Int32`, `instEq0String`, `instEq0Char`
  and `instEq0Bool` are elaborated while their own `Eq0` instance does not
  exist yet. Their body `x == y` therefore falls through to the 500 star
  instances, and the newest of those is the comparator bridge.
- `instEq0LemOrdering` uses its derived BEq, and `instEq0Unit` is `true`.

### 2.3 Precedence between specific and star instances

At equal priority, a **specific** instance beats the star bridge whatever the
declaration order. Examples:

- `BEq (List Nat)` resolves to the older core `List.instBEq`, not the newer
  bridge.
- The same holds for `Pset`, `Fmap`, `Sum` and `Prod`.
- A generated type's derived `BEq` wins for the same reason. The probe below
  mimics `Symbol.identifier`, with a derived BEq, a 500 auto trio and a
  name-only model `Eq0`:

  ```
  #synth BEq identifier   ⟶ instBEqIdentifier
  #synth Eq0 identifier   ⟶ instEq0Identifier_1
  ```

[AGENT] The lattice note says the derived instance wins "by newest-declaration
order". It actually wins by discrimination-tree specificity. The result is the
same, but the note should say so when it is next touched.

Lem's `=` reaches Lean resolution only at three kinds of site. At known types,
Lem inlines the model's class method itself: the prio_pair model wins through
the inlined body, per `tests/comprehensive/lean-test/TestInstancePriorityCheck.lean`.

1. Target reps that map to `==` at base types: `natEq`, `intEq`,
   `stringEquality`, `charEqual` and `unsafe_structural_equality`. Their OCaml
   meaning is structural `=` (basic_classes.lem:56-63, num.lem:255-258).
2. Polymorphic `[Eq0 a]` code, where the bridge applies to an abstract
   dictionary.
3. Bodies of derived `BEq` instances on the fields of generated types. OCaml's
   structural equality ignores Lem instances here.

## 3. Consumer census (measured; instrument = scratch Lean script)

The census walked the value of every declaration in the generated modules and
recorded each application of a bridge. For each site it recorded the type
argument and the `Eq0` argument. In the counts below, "decls" is the number of
declarations that contain the pair. A declaration can appear in more than one
row.

**cerberus**: the cerberus-sl pinned workspace (`.cerberus-ws`, cerberus-lean
`2b51d2a57`, LemLib `38f87d5`). 33959 generated declarations were scanned.
Rows that change under the recommendation:

```
335 decls  instBEqOfEq0 @ Nat / Lem_Num.instEq0Nat_1
228 decls  instBEqOfEq0 @ Int / Lem_Num.instEq0Int_1
117 decls  instBEqOfEq0 @ String / instEq0String_symbol     ← cerberus Symbol.lean's model `Eq digest` (digest renders as String)
  6 decls  instBEqOfEq0 @ String / Lem_Basic_classes.instEq0String
 96 decls  … @ Bool,  23 @ Char,  17 @ Unit
 66 decls  … @ abbrevs of Nat/Int (allocation_id 11, StorageInstanceId 9, thread_id 8, loop_id 7, reg 6, Address 6, aid 4, scope_id 2, provenance_id 2, SymbolicStorageInstanceId 1, thread_id0 1, tid 1)
           — of which pre_execution 6, type_predicate 1, dlist 1 do NOT switch (no DecidableEq)
 23 decls  instBEqOfMapKeyType @ UInt64 (19) / UInt32 (2) / UInt8 (2)
```

Derived total: about 903 row-declarations switch (the upper bound on distinct
declarations). 21 polymorphic `<non-const>` sites stay on the bridge.

**linksem**: `linksem-lean` `f6293f5`, LemLib `77ad4fa`. 11799 declarations
were scanned. Rows that switch: Nat 440, String 107, Uint32_wrapper.uint32 72,
Bool 24, Uint64_wrapper.uint64 22, Int 21, Char 11, UInt8 9 (comparator), and
small aliases totalling 30. Derived total: about 736. 14 polymorphic sites
stay. Some of the `Eq0` arguments are linksem's own model instances
(`instEq0Uint32_elf_types_native_uint*`, `instEq0Uint64_…`) on `abbrev uint32
:= Nat`. Their bodies are `isEqual := (fun x y => x == y)`
(`Elf_types_native_uint.lean:98-102` etc.), so they chain back to LemLib's Nat
equality.

The simulated resolution, measured in each consumer environment, is verbatim
in the same shape for every switching type. Erase the three bridges, then
re-add `instBEqOfEq0` at 450 and the comparator bridges at 400:

```
TODAY | Nat    | BEq := (some Lem_Basic_classes.instBEqOfEq0) | DecidableEq? true | LawfulBEq? false
OPT-A | Nat    | BEq := (some instBEqOfDecidableEq)           | DecidableEq? true | LawfulBEq? true
TODAY | UInt64 | BEq := (some Lem_Map.instBEqOfMapKeyType)    | DecidableEq? true | LawfulBEq? false
OPT-A | UInt64 | BEq := (some instBEqOfDecidableEq)           | DecidableEq? true | LawfulBEq? true
OPT-A | pre_execution | BEq := (some Lem_Basic_classes.instBEqOfEq0) | DecidableEq? false | LawfulBEq? false
```

Census-visibility:

- No consumer `generated/*.lean` text changes under any option. The bridges
  are emitted only into LemLib, unless a consumer's Lem model declares its own
  class with an `==`-mapped or comparator method, and neither consumer does.
- The cerberus failure census is lexical over generated text, so it does not
  move.
- The failure-reach gate's kernel dependency closure does move: `defaultCompare`
  and `instBEqOfSetType` leave many closures. Neither contains a
  `failwithI`/`panic!` site, so the register should not move. Expected,
  pending `check_failure_reach.sh`.
- The axiom census does not move: the core instances are axiom-free.

## 4. Options

### (a) Lower the `Eq0` bridge below core and the comparator bridges below it — RECOMMENDED

`instBEqOfEq0` moves to 450, and `instBEqOfSetType`/`instBEqOfMapKeyType` move
to 400. Lowering only the `Eq0` bridge to 500 or below is **not enough**:

- At 500 it ties with core, and as the newer instance it still wins.
- Below 500 without moving the comparator bridges, the comparator bridges (500,
  newer than core) would win at Nat. This was measured: today `UInt64`
  resolves to `instBEqOfMapKeyType`.

The order 1000 (derived/model/specific) > 500 (core DecidableEq) > 450 (`Eq0`
bridge) > 400 (comparator bridges) > 100 (generic defaults, residuals) keeps
every relation in today's lattice, with two exceptions. Core now beats the two
LemLib bridges, and the order inside the arc-14 R3 de-tie (Eq0 bridge over
comparator bridges) is unchanged.

- **Values.** At every base type, today's `==` equals core's `decide (a = b)`.
  These kernel theorems were checked against today's LemLib (scratch probe,
  `#print axioms` = `[propext, Classical.choice, Quot.sound]`):

  ```lean
  theorem cmpBEq_eq_decide {α : Type} [Ord α] [Std.LawfulEqOrd α] [DecidableEq α] (a b : α) :
      (match defaultCompare a b with | LemOrdering.EQ => true | _ => false) = decide (a = b)
  theorem bridgeNat_eq_decide (a b : Nat) : (a == b) = decide (a = b) := cmpBEq_eq_decide a b
  -- likewise Int, String, Char, Bool, Int32, Int64, UInt8, UInt64 (comparator form); Unit by cases
  ```

  The only consumer model instance on the switching path is cerberus's
  `Eq digest`, `digest_compare x y == 0`. It is value-equal by the existing
  `CerbCtypeMeasure.digest_compare_eq_zero_iff`:
  `(digest_compare x y == 0) = true ↔ x = y`. linksem's are `x == y` chains.
  At the target-rep sites (§2.3), core structural equality is exactly the
  OCaml meaning.
- **Terms.** About 903 cerberus and about 736 linksem declarations change their
  elaborated `==` (§3, derived).
  - Generated text does not change. In LemLib, only the three priority
    lines change.
  - LemLib's base `Eq0` bodies re-elaborate to core:
    `instEq0Nat := … @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) …`
    (measured).
  - Linksem's and cerberus's `x == y` model bodies re-elaborate to core in the
    same way.
- **Coherence.**
  - `@instBEqOfEq0 Nat Lem_Num.instEq0Nat_1 = instBEqOfDecidableEq` holds by
    `rfl` (measured), so the diamond that remains in polymorphic code instantiated
    at Nat is definitional.
  - Residual risk: a future model `Eq` on a Lem alias of a base type. Two cases:
    - An equality coarser than `=` where Lem does **not** inline the method
      would switch from the model to structural equality.
    - Today, no such site exists in either consumer (§3 lists every switching
      `Eq0`). This is covered by the census at re-pin (§6), not by priority.
- **Lattice probe.** `TestInstancePriorityCheck.lean` (prio_pair model-wins,
  prio_auto, prio_coarse de-tie) passes under (a). It was compiled against the
  modified scratch LemLib with exit 0. A model-only type with no derived BEq
  still gets the bridge (`#synth BEq modelOnly ⟶ @instBEqOfEq0 modelOnly …`).
  Polymorphic `[Eq0 a] [SetType a]` code still gets the `Eq0` bridge, not the
  comparator bridge (`polyEq` printed `@instBEqOfEq0 a inst`).
- **Proofs.** Probe `P8`. Under (a) it builds with exit 0. Under today's
  LemLib, every leg fails (verbatim errors below):

  ```lean
  example (a b : Nat) (h : (a == b) = true) : a = b := by simpa using h        -- E1
  --   today: "Type mismatch: After simplification, term h has type (a == b) = true but is expected to have type a = b"
  example (a b : Nat) (h : (a == b) = true) : a = b := eq_of_beq h             -- E2
  --   today: "failed to synthesize instance of type class LawfulBEq Nat"
  example (a b : Int) : (a == b) = decide (a = b) := rfl                       -- E3
  --   today: "Type mismatch rfl …"
  theorem elem_iff (a : Nat) (l : List Nat) : Lem_List.elem a l = true ↔ a ∈ l := by
    induction l with
    | nil => simp [Lem_List.elem, listMemberBy]
    | cons x xs ih =>
      simp only [Lem_List.elem, listMemberBy, Bool.or_eq_true, List.mem_cons] at ih ⊢
      rw [ih]; simp                                                            -- E4
  --   today: "`simp` made no progress"
  ```

- **Derived comparisons for generated types.** Derived `BEq` bodies on
  base-type fields now use core equality. That makes `deriving BEq, ReflBEq,
  LawfulBEq` succeed (E5 below), where today the deriving handler is left with
  unsolved `(a == a) = true` goals. Derived `Ord`, `SetType`/`Ord0` trios and
  model instances are unchanged.

  ```lean
  inductive tag2 where | A : Nat → tag2 | B : String → Int → tag2
    deriving BEq, ReflBEq, LawfulBEq                                            -- E5
  example (x y : tag2) (h : (x == y) = true) : x = y := by simpa using h
  ```

  Emitting `LawfulBEq` from the backend is a possible follow-on and is not part
  of this decision.

### (b) Keep the bridge; add `LawfulBEq` instances and `simp` lemmas for it

Add `instance : @LawfulBEq Nat (instBEqOfEq0 Nat instEq0Nat_1)` and the same
for each base instance, proved through `bridge*_eq_decide`.

- **Values and terms.** Nothing changes.
- **Coherence.** No resolution risk.
- **Proofs.** E1, E2 and `simp [h]` then work (measured with a local instance
  for Nat). Statements that need core's instance up to `rfl` still fail: `(a ==
  b) = decide (a = b) := rfl` and `= Nat.beq a b := rfl` (measured).
- **Limits.**
  - `LawfulBEq` is keyed on the exact `Eq0` term, so it fragments. Each consumer
    model instance needs its own: cerberus's 117 digest `String` sites, and
    linksem's `uint` model `Eq0` instances (10 distinct in the census). Otherwise the gain stops at those
    sites.
  - LemLib's base `Eq0` bodies keep the comparator route.
  - A generic `LawfulBEq` for the bridge is impossible, because `Eq0 (Pset a)`
    is set equality.

### (c) Define base `Eq0` instances through core

Mechanism: lower only the comparator bridges to 400. Base `Eq0` bodies then
re-elaborate to `instBEqOfDecidableEq`, while use sites keep `instBEqOfEq0` at
1000.

- **Values.** Unchanged (§4a theorems).
- **Terms.** Use sites are unchanged, except the comparator `UIntN` sites (23
  in cerberus, 9 in linksem), which move to core. LemLib's base `Eq0` bodies
  change.
- **Proofs.** All of E1-E5 pass (measured). `#synth LawfulBEq Nat ⟶
  Nat.instLawfulBEq` is found against the bridge term by unfolding the
  reducible instances.
- **The gap.** It holds only where the `Eq0` chain ends in LemLib.
  - A digest-shaped model instance, `instance : Eq0 String where isEqual x y :=
    digest_compare x y == 0`, still fails E1 under (c). Verbatim: "Type
    mismatch: After simplification, term h has type (a == b) = true but is
    expected to have type a = b".
  - The same probe passes under (a): `#synth BEq String ⟶ @instBEqOfDecidableEq
    String instDecidableEqString`.
  - In cerberus this gap covers 117 of the 123 `String` sites.
- **Consumer impact.** Smaller churn than (a): lemma statements that name
  `instBEqOfEq0` keep matching syntactically.

### (d) Retire the `Eq0` → `BEq` bridge entirely

Emit `isEqual` for Lem `=` in polymorphic code, and keep `==` only for target
reps at base types.

- **Values.** Unchanged.
- **Terms.** Large text churn in LemLib and in every generated module with
  `[Eq0 a]` code (polymorphic sites: 21 cerberus, 14 linksem, plus LemLib
  internals such as `elem`, `isPrefixOf` and Fmap equality).
- **Coherence.** Best: LemLib then injects no star `BEq` at all.
- **Proofs.** Same as (a), plus `isEqual` is never hidden behind `==`.
- **Cost.** Hand-written consumer `==` on model-only types breaks. One example
  is a type whose only equality is a model `Eq0`, and the probe's `modelOnly`
  shows that shape. [AGENT] Not recommended now. It is the structural end
  state if (a)'s residual risk (§4a coherence) ever materialises.

### Options table

| | (a) 450/400 | (b) LawfulBEq on bridge | (c) comparators 400 only | (d) drop bridge |
|---|---|---|---|---|
| Value parity | kernel-proved per base type; consumer instances checked | trivially | as (a) | as (a) |
| Generated text change | none (LemLib: 3 lines) | none (+ instances) | none (LemLib: 2 lines) | large |
| Elaborated-term change | ~903 cerberus / ~736 linksem decls (derived) | 0 | 23 / 9 use sites + LemLib bodies | large |
| `LawfulBEq`/`simp`/`rfl`-to-`decide` | everywhere | LemLib types only, no `rfl` | LemLib-ending chains only | everywhere |
| Coherence risk | coarse model `Eq` on a base alias would switch (none today) | none | none new | none |
| Consumer proof churn | 2 cerberus + 9 cerberus-sl lemmas | none | the same `show` lemmas (bodies change) | larger |

## 5. Consumer exposure (read-only)

Hand-written trees: cerberus-sl at `6edb0c4`, covering `CerberusIris/`,
`CerberusSL/`, `CerberusRefined/`, `Corpus/Capture/`, `Spikes/` and
`probes/`, and excluding `.lake`, `.cerberus-ws` and the quoted corpus. Also
cerberus-lean `lean_frontend` top level plus `test/` and `speclab/`, and
linksem `handwritten/`.

- **Break under (a), (c) and (d).** These proofs `show`/`change` to the
  comparator body:
  - cerberus-lean `CerbCtypeMeasure.lean:341` `natEq0_iff`. Its
    `symEq_iff:356` `show` re-elaborates consistently but uses `natEq0_iff`.
  - cerberus-sl `CerberusIris/Env.lean:30` `lemNatBeq_iff` and `:38`
    `lemNatBeq_eq_decide`. Both statements name `@instBEqOfEq0 Nat
    Lem_Num.instEq0Nat_1`.
  - cerberus-sl `Lang.lean:178` `lem_nat_beq_iff`, `EvalArms.lean:1597`
    `lem_int_beq_iff`, `Repr.lean:29` `int_beq_refl`, `Repr.lean:411`
    `lem_nat_beq_self`, `Call.lean:182` (inside `call_proc_eq`), and
    `CerberusSL/StdLibEq.lean:33`, whose statement names the bridge.

  All of them become `beq_iff_eq`/`beq_self_eq_true`/`rfl`. If names and
  statements are kept, about 64 downstream uses in cerberus-sl and 7 in
  cerberus-lean are untouched (derived from the read-only grep). Under (a), the two statements that name the
  bridge still typecheck, but they no longer match generated `==`
  syntactically. Restate them with `==`.
- **To be verified by the cerberus-sl build.** `simp only [..., beq_iff_eq]`
  at `Recon/Admit.lean:742` and `Recon/Arena.lean:393` is inert on the bridge
  today and fires under (a). The goal shapes after them may change.
- **Get easier.** Every lemma above exists only because `LawfulBEq` is
  missing. `Repr.lean:831` already hedges both forms (`first | exact
  int_beq_refl id | exact beq_self_eq_true id | simp`).
- **Unaffected.** linksem's hand-written code has zero exposure. There are no
  hand-written `BEq`/`Eq0` instances at a base type in any tree. The `decide`
  closers (762/55/3) are on concrete facts.
- **Under (b).** Nothing breaks and little gets easier: digest and linksem
  sites stay unlawful.

## 6. Recommendation and verification plan [AGENT]

Adopt **(a)**: `instBEqOfEq0` at 450, and `instBEqOfSetType`/`instBEqOfMapKeyType`
at 400. It is one lem arc, then a re-pin.

1. **lem-lean.**
   - Change the two emission sites in `src/lean_backend.ml` (4634-4639,
     4641-4654) and their comments.
   - Regenerate LemLib. The diff should be exactly the 3 priority lines.
   - Update the lattice note: add a core-500 row, the new 450/400 rows, and
     the specificity rule (§2.3). Retire the "deliberate tie 1" text. Update
     DESIGN.md's priority paragraph.
2. **Probes, plant-tested.**
   - Extend `TestInstancePriorityCheck.lean` with base-type legs:
     `#guard_msgs in #synth BEq Nat` expecting `instBEqOfDecidableEq`,
     E1/E2 at Nat, Int, String and Char, the polymorphic leg, and the
     model-only leg.
   - Add the `rfl` agreement theorems `Eq0.isEqual (α := T) = fun a b =>
     decide (a = b)` for the LemLib base types to `LemLibTheorems`.
   - Plant: restore 1000 on the bridge, and the base legs must fail.
   - [AGENT] I propose these as speedbump tests. They pin the elaboration
     property, which is not a trust property. The trust property, value
     parity, is carried by the theorems and the differential lanes.
3. **Census at re-pin, one-off.** Re-run the §3 instrument on both consumers.
   Every switching `(type, Eq0)` pair must be either a LemLib base instance or
   carry a value-agreement theorem. Today the only non-LemLib pair is
   cerberus's digest, already proved. The census also catches the §4a residual
   risk.
4. **cerberus-lean re-pin.**
   - Run the full battery per `scripts/LADDER.md`/VALIDATION.md,
     cache-disabled, because elaboration changes. This includes the
     differential baselines, `check_failure_reach.sh` and the axiom gate.
   - Re-prove `natEq0_iff` and `symEq_iff`.
5. **Consumers.**
   - Send a re-pin note to cerberus-sl listing the nine lemmas and the two
     `simp only` sites, then run a full cerberus-sl build.
   - linksem: rebuild plus `diff_main_elf.sh`.

**Effort.**
- lem side: S, about half a day, including the probes and the lattice/DESIGN
  edits.
- cerberus re-pin: the usual re-pin and gate cost, plus about an hour of proof
  edits.
- cerberus-sl: S to M (its own slice).
- No grind risk: LemLib builds in about a minute, and the full LemLib build
  with tests was green under (a) (39 jobs).

## 7. Method notes

- Scratch probes ran in a detached worktree at `5dfcd25`, now removed. Options
  (a) and (c) were simulated by hand-editing the generated `Basic_classes.lean`
  and `Map.lean` priorities there and rebuilding. Nothing was committed from
  it.
- Consumer censuses loaded each consumer's existing oleans by calling `lean`
  directly through `capped` with an explicit `LEAN_PATH`. Lake was not invoked.
- [AGENT] Incident, recorded for the record: an earlier census attempt ran
  `lake env` in the primary `cerberus-lean/lean_frontend` checkout.
  - The first run did not source `env.sh`, and a second run with it then
    re-cloned `.lake/packages/LemLib` at the manifest rev (`77ad4fa`), dropping
    its oleans.
  - They were rebuilt in place with `scripts/ce … capped lake build LemLib`
    (33 jobs, green).
  - That checkout's `CerberusLean` oleans had already been stale before this
    (generated sources from 2026-09-28 against oleans from 2026-09-25), so
    nothing that was current was lost.
