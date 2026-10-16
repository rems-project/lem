# Parity-fix slice record — 2026-09-03

Provenance: parity-fix worker slice on branch `arc/lem-parity` (base
mainline `mdd/lean-backend` @ bc1bae7), briefed on the noodler's
findings (`2026-09-03_noodle-backend.md`, branch `noodle/backend`
@ a02cb6f5a). Rulings that govern every disposition below, paraphrased:

- [USER 2026-09-03]: the discrepancies found are to be *fixed*, not
  recorded as documented discrepancies (specifically the left-to-right
  v. right-to-left one); the LEM semantics is followed. The OCaml
  target is the reference semantics of a lem program; the Lean target
  must compute the same thing.
- [USER 2026-09-03]: the aim with lem-lean is zero behavioural
  discrepancies between the OCaml reference and Lean; every such
  discrepancy is by definition a bug unless an extraordinarily
  compelling case against that is made now, and all legacy permission
  is revoked as of that date.
- [USER 2026-09-03] agreed on the two exceptions: (a) failure-path
  MESSAGE TEXT may differ — failure-vs-success must agree per program
  (Lean fails exactly where OCaml fails; a Lean SUCCESS where OCaml
  raises is a FIX); (b) RESOURCE LIMITS, direction-sensitive — Lean
  must not fail where the OCaml reference succeeds; the converse is
  acceptable.
- [USER 2026-09-03]: *missing features* are allowed deviations if they
  are cleanly identified — (c) a construct the Lean backend does not
  support may be REFUSED at generation time with a loud,
  construct-naming error; emitting something that computes a
  different result, or silently dropping, is never allowed.

All judgments below are [AGENT] unless marked; quoted outputs are
verbatim; tallies marked "derived" are derived.

## 0. Method: the two-target parity runner

`tests/comprehensive/parity/run.sh` (suite phase `lean-parity`, the
noodler's `run_parity.sh` landed as the suite's real runner). For each
`parity/probes/<p>.lem` it builds an OCaml native binary (against
`ocaml-lib/_build_zarith`, OCaml 5.4.0) and a Lean binary (against this
checkout's `lean-lib`, Lean 4.28.0, through `scripts/capped`), runs
both, diffs stdout byte-for-byte, and checks the OCaml output against
its committed pin `parity/expected/<p>.out` (drift = FAIL; rebaseline
is explicit, `REBASELINE=1`, and committed). Failure probes (`f_*`)
must FAIL on both targets (Lean under `LEAN_ABORT_ON_PANIC=1`) after an
identical stdout prefix (class (a)); each step takes a runtime `nat` so
neither compiler folds the failing operation into initialisation.
`expected_failures.txt` lists probes whose divergence has a REGISTERED
fix in flight; a listed probe that passes fails the suite (a stale
entry cannot survive). Vacuity guards: missing pin, empty reference
output, unbuilt exe, a failure probe whose reference succeeds.

The retired M2 scaffold (`TestIntegerDivParity.lean`, phase
`lean-div-parity`) compared Lean against HAND-MEASURED literals and
never built an OCaml binary; it is deleted, and an honesty note is
appended to `2026-08-31_L0-fix-first-record.md` item 5. Its values were
correct (the runner confirms the `integer` rows byte-for-byte).

Red baseline (this runner, pre-fix lem @ bc1bae7 + LemLib @ bc1bae7),
derived tally: 9 probes FAIL (p_cmp_order, p_eval_order, p_keywords
[Lean build error], p_list_deep [stack overflow], p_map_beq,
p_num_div, p_show, p_str_bytes, p_str_escapes), 8 OK (p_functions,
p_hello, p_list_ops, p_monad, p_num_misc, p_patterns, p_precedence,
p_records). The red diffs are quoted per finding below (they are the
noodle record's diffs, reproduced by this runner).

## 1. Per-finding record

### F8 — top-level names that are Lean tokens / root declarations (INVALID-OUTPUT)

Reference: the OCaml target emits `let from ...`, `let main ...`
verbatim (valid OCaml). Mechanism: lem's top-level rename pass avoids
the names in `library/lean_constants` (`Initial_env.read_target_constants`;
`rename_top_level.ml:get_fresh_name`) — `at`/`by`/`ite` were already
renamed `at0`/`by0`/`ite0`; `from`, `termination_by`, `decreasing_by`,
`elab`, `main`, `dite` were missing.

Fix: `library/lean_constants` regenerated from BOTH deployed toolchains
(`gen_lean_constants.lean` run under 4.28.0 and 4.32.2, union, 498
names; the generator now carries the hand-added keyword rows and the
contextual tokens so regeneration is reproducible); `lean_syntax_keywords`
(the «»-escape table for locals) gains the missing tokens.

Red (noodle record, verbatim): `error: P_keywords.lean:43:3: unexpected
token 'from'; expected identifier` … `` `main` function must have type
`(List String →)? IO (UInt32 | Unit | PUnit)` `` … `` `dite` has already
been declared``. Green (runner, verbatim): `=== p_keywords === / OK:
parity (91 lines byte-identical to the OCaml reference; pin matches)`.
Suite: `test_keywords.lem` F8 section (asserts `kw_f8_from`,
`kw_f8_use`). Generated names: `from0`, `termination_by0`,
`decreasing_by0`, `elab0`, `main0`, `dite0` (probe `kw.lem`, verbatim
`def  from0   (x  : Nat)   :  Nat :=  x  +   1`).

Consumer impact: 213 more root names are avoided (e.g. `inline`, `Sep`,
`mt`, `One`); any cerberus generated definition carrying one of them is
renamed (`One` → `One0` was observed in a probe); hand-written cerberus
Lean referencing such a generated name breaks at compile time (loud).

### F4 — derived `Ord` constructor rank on single variants (DISCREPANCY)

Reference: OCaml polymorphic `compare` (runtime/compare.c) ranks every
nullary constructor (immediate) below every non-nullary one (block),
declaration order within each class, fields lexicographically; records
by field declaration order. Lean's `deriving Ord` ranks by declaration
index — equal to OCaml's exactly when no nullary constructor is declared
after a block constructor.

Fix (`src/lean_backend.ml`): `texp_needs_ocaml_rank` (a nullary
constructor after a block one) routes SINGLE variants through the
existing arc-10 `ctor_rank_ocaml` derivation as a block of one
(`derived_comparison_single`, both the single-type and the
mutual-of-one paths; `tyexp` and `generate_beq_ord_instances` suppress
`deriving` for them). Records and all-nullary/all-block variants keep
`deriving` (provably the same order). A mixed variant whose fields
reference it under a head the derivation cannot recurse through
(anything but list/maybe/either/tuple) is REFUSED at generation time
with the workaround named (`skip_instances` + hand instance) — the
alternatives (wrong order, or a panicking residual where OCaml
compares) are both divergences.

Red (verbatim): `< F vs B0: LT / < B5 vs C: GT / > F vs B0: GT / > B5 vs
C: LT` and the set/sort rows. Green (verbatim): `=== p_cmp_order === /
OK: parity (45 lines byte-identical to the OCaml reference; pin
matches)` — the probe was extended with a recursive and a polymorphic
mixed variant (`TLeaf vs TNode(TLeaf,0)`, depth rows, `PNone vs PSome`)
and `choose`; pin rebaselined from the OCaml run. Suite:
`test_derived_comparison.lem` F4 asserts (8 rows: rank, declaration
order, field lex, recursive root and depth, structural BEq).

Consumer impact: the read-only scan of `cerberus-lean/lean_frontend/generated`
— CRITERION: a top-level `inductive … deriving BEq, Ord` (single, not in a
`mutual` block) with a nullary constructor declared after a
non-nullary one, matched textually by a regex over the emitted
constructor lines — finds 35 of 170 (derived tally; the auditor's
40/188 uses a different criterion, presumably including the
`Foo_auxiliary`/handwritten-copy files or mutual members; the sets
overlap on every name checked). E.g. `Symbol.symbol_description`,
`Symbol.prefix0`, `Errors.*_cause`, `Cn.cn_base_type`. Self-referential
among them: `AilSyntax.constant`, `Cn.cn_base_type`,
`Core_typing_aux.inferred`, `GenTypes.genIntegerType`, `GenTypes.genType`
— under list/maybe/tuple heads as far as the scan shows, so they derive;
a refusal there would be loud at the pin bump. `Set.choose` (comparator minimum) and `Core_linking.topo_order`
may move TOWARD the oracle; the cerberus differential battery is the
gate (not run here).

### F6 — evaluation order of multi-draw expressions (DISCREPANCY)

Reference (compiled OCaml probe, `p_eval_order.lem` + impure counter
`p_eval_order.ext.ml`, pin verbatim): `tuple: (1, 0) / app2: (3, 2) /
app3: [6; 5; 4] / list: [9; 8; 7] / record: (11, 10) / cons: [13; 12] /
arith: 164 / nested: (18, (17, 16)) / lets: (19, 20) / head: (22, 21) /
record_rev: (25, 24) / ctor: (27, 26) / ctor_tuple: (2829, 2829) /
nested_app: (32, 30) / cmp: (false, 35) / str: 37-36 / if: (0, 39) /
match: (0, 41) / field: 42 / just: Just ((45, 44)) / just1: Just (46)`.
Rules established from it: OCaml evaluates the subexpressions of one
node RIGHT-TO-LEFT — application arguments and then the head
(`head`), tuple components, constructor arguments, list elements,
infix operands (`arith`, `cmp`, `str`), record fields: the
labels are sorted to their DECLARATION order, then evaluated
right-to-left — the LAST-DECLARED field first, whatever the source order
(`record_rev`: type `<| fa; fb |>`, construction `<| fb = fresh (); fa =
fresh () |>` gives `(25, 24)`: `fb`, last declared, drew 24 first) — and
`let`/`if`/`match` as written.

Fix (`supply_thread`/`supply_thread_app`): `supply_thread_list` folds
from the right; infix operands right first; record fields sorted by the
type's `type_fields` before threading and rendered back in source
order; the general-head branch hoists the arguments and then the head.
Pure (non-supply) emission is untouched (corpus tree-diff §3).
DESIGN.md/manual: "left-to-right depth-first … reproduces the effectful
counter's dynamic draw order" replaced by the true statement.

Red (verbatim): `< tuple: (1, 0) … > tuple: (0, 1)` (8 rows) — the red
is reproducible only on the probe's pre-F5 rows: the rows added for F5
(`just`, `just1`) and the F6 extension were REFUSED by the pre-fix
backend (F5's misdescribed error), so the extended probe does not
generate on bc1bae7 at all. Green (verbatim): `=== p_eval_order === /
OK: parity (21 lines byte-identical to the OCaml reference; pin
matches)`; `=== p_supply_shapes === / OK:
parity (35 lines …)` — the second probe runs every shape of
`test_supply.lem` on both targets (OCaml counter reset to the seed per
shape) and is the source of the kernel pins in
`TestSupplyCheck.lean`/`TestSupplyDraws.lean`, which now quote it (e.g.
`draw_list 5 = [6; 5] @ 7`, `mk_srec 7 = (8, 7) @ 9`, `pair_draw 30 =
(31, 30) @ 32`, `fuel_draws 60 = [61; 60] @ 62`). Short-circuit forms
(L1 MAJOR-1) unchanged (`sc_*` rows identical).

Deviation-4 (L1 record): a drawing TOP-LEVEL VALUE binding is evaluated
once at module initialisation by OCaml; per-use state passing cannot
mirror that → REFUSED at generation time (`lean_supply_prepass`,
threading arity 0), a class-(c) refusal replacing a behavioural
divergence. `test_supply.lem`'s `let (top_a, top_b) = pair_draw ()`
moved to `negative/neg_supply_toplevel_value.lem` (rejected as
declared). Deviation-5 (target_rep'd defs excluded from lifting): not a
backend divergence — a target rep is the model author's equivalence
claim on every target; documented, kept. Deviation-3 (`natural`
accepted by G-type): not behavioural; kept.

Consumer impact: Lean-side symbol numbering moves again at the pin
bump wherever a cerberus expression draws twice (the 19 catalogued
sites; single-draw expressions such as `Symbol (digest ()) (fresh_int
()) SD_None` are unaffected); id-canonicalized lanes unaffected; the
uri diagnostic row embedding a Lean symbol id (C1-F2) re-records.

### F5 — draw under a target_rep'd library constructor (ODDITY → SUPPORTED)

Root cause: the shared application renderer REBUILDS argument nodes
(identifier-form reps inline to `App (Backend rep, args)`;
`mk_opt_paren_exp` re-creates spines), so the transform's
physical-identity substitution memo missed and the argument fell to the
pure emitter, whose supply net refused it with a misleading message.
Fix: threaded values carry their variable name (`lean_sval = SVar |
SPure`); drawing arguments of a pure head are materialised as real `Var`
expressions (`supply_atomize_args`; a compound threaded value is first
let-bound) and rendered by the ordinary machinery — `Just (fresh (),
fresh ())`, `Left (fresh ())`, `fst (fresh (), fresh ())`, `Just (One
(fresh ()))` all thread. Green: `p_eval_order` rows `just`, `just1`;
`p_supply_shapes` row `mk_just 40 = Just ((41, 40)) @ 42`; kernel pin
`mk_just 40 () = (some (41, 40), 42)`. `negative/neg_supply_ctor_arg.lem`
deleted (the shape is positive now).

### F1 — `int`/`int32`/`int64` div and mod (DISCREPANCY)

Reference (`ocaml-lib/nat_num.ml:12-33`, verbatim): `let int_mod i n =
let r = i mod n in if (r < 0) then r + n else r` / `let int_div i n =
let r = i / n in if (i mod n < 0) then r - 1 else r` over OCaml's
truncating `/`,`mod` (and the Int32/Int64 `div`/`rem` twins). NOT
Euclidean for a negative divisor; `integer` (Nat_big_num.div, Euclidean)
is the M2-verified control and is unchanged.

Fix: LemLib `lemIntDiv/lemIntMod/lemInt32Div/lemInt32Mod/lemInt64Div/
lemInt64Mod` (each with the OCaml text in its docstring); `num.lem`
Lean reps repointed. Red (verbatim): `< integer -7 -2 div=4 mod=1 /=4 |
int div=2 mod=-3 /=2 | int32 div=2 mod=-3 | int64 div=2 mod=-3` vs `>
… | int div=4 mod=1 /=4 | int32 div=4 mod=1 | int64 div=4 mod=1`. Green
(verbatim): `=== p_num_div === / OK: parity (11 lines byte-identical to
the OCaml reference; pin matches)`. Suite: `test_integer_div.lem` F1
asserts quote the pin rows (a first draft had two rows wrong; the suite
caught it — the values now in the file are the pinned ones).

### N3 — `int32`/`int64` had no overflow (census FIX, with F1)

Lem `int32`/`int64` are now Lean `Int32`/`Int64` (wrapping two's
complement, like OCaml's); conversions mirror `Int32.of_int` (modulo
2^32), `Nat_big_num.to_int32` (Overflow → loud failure), `Int64.to_int32`
(low bits), `Int64.of_int32` (sign extension); bitwise ops and shifts
over the machine types; `int32Asr`'s m10 positive-branch bug disappears
with the representation. Probe `p_int_wrap.lem`, green (verbatim):
`OK: parity (42 lines byte-identical …)`; rows include `max32 + 1:
-2147483648`, `abs min32: -2147483648`, `of_int 2^32+5: 5`,
`from_int64 low bits: 5`, `min32 div -1: -2147483648`, `pow wraps:
1870418611`, `lsr min32 31: 1`. Failure probe `f_int32_overflow` (both
fail after `before: in range: 2147483647`). Manual limitation row
removed.

### D1 — division by zero totalised to 0 (census FIX; class (a) direction)

Every division/remainder rep (`nat`, `natural`, `int`, `integer`,
`int32`, `int64`, `integerDiv_t/Rem_t/Rem_f`, mword `unsignedDivide`/
`signedDivide`/`modulo`) fails loudly on a zero divisor
(`failwithI "Division_by_zero"`) where OCaml raises. Failure probes
`f_div_zero`, `f_int_div_zero`, `f_integer_mod_zero` (both targets fail
after identical prefixes). The first runs exposed a second latent
defect class (R1 in the census): CLOSED-TERM EXTRACTION lifted panicking
closed applications to module-initialisation constants, where the panic
fires silently (messages are off during init) and the constant becomes
the `Inhabited` default — so (i) `7 / 0` printed `at zero: 0` with no
PANIC line (the `@lemDivByZero Nat _` constant), and (ii) EVERY binary
importing `LemLib.Num` aborted at start-up under `LEAN_ABORT_ON_PANIC=1`
before printing anything (the generated `NumAbs LemRational` instance
contains the literal `(0 : rational)` = `unsupportedRationalFromNumeral 0`,
a closed panicking term; verbatim from the IR:
`_init_lp_LemLib_Lem__Num_instNumAbsLemRational___lam__0___closed__0 ::
x_2 = lp_LemLib_unsupportedRationalFromNumeral(x_1);`). This is the
mechanism behind the L0 record's "abort fires at module INIT"
observation. Fix: `@[never_extract]` on `failwithI`/`fuelExhaustedWith`
AND their `implemented_by` targets (the compiler substitutes the
implementation before extraction), on `lemDivByZero`, and on every
panicking helper (`unsupported*`, `rationalNumerator/Denominator`,
`realSqrt/Floor/Ceiling`, `THE`, `natLnot`, `lemDebugPrintUnsupported`).
Measured after the fix: `import LemLib.Pervasives_extra` under
`LEAN_ABORT_ON_PANIC=1` exits 0; the `lean-panic` suite phase's leg 2
now aborts at the program point (its Makefile note updated).

### F7 — deep lists (DISCREPANCY; class (b) direction)

Measured (compiled sweep, 300 000 elements, this LemLib; verbatim
`Stack overflow detected. Aborting.` on): core `List.zip`, `List.unzip`
(even `List.unzipTR` called directly), generated `Lem_String.concat`,
`Lem_Show.stringFromListAux`, `Lem_List.deleteFirst`, `update`,
`catMaybes`, `mapiAux`, `Lem_List_extra.init`, `zipSameLength`,
`unfoldr`, `Lem_Sorting.insertBy`, and `List.foldr` as called from
`Lem_List_extra.foldr1` (the same `List.foldr` call worked in a
polymorphic local definition — the core `@[csimp]` replacements were
measured not to apply reliably at these call sites, so no fix relies on
them). OK at 300 000: length, foldl, map, filter, append, flatten,
replicate, take/drop, reverse, all/any, find/lookupBy, elem,
listEqualBy, partition, concatMap, splitAt, dropWhile/takeWhile,
findIndex/findIndices, isPrefixOf, lexicographic compares, snoc,
dest_init, mapMaybe, foldl1, stringConcat, String.ofList/toList, show,
setFromListBy, sort_by_ordering.

Fix: explicit accumulator loops / an Array fold in LemLib (`lemListZip`,
`lemListUnzip`, `lemListFoldr`, `lemListDeleteFirst`, `lemListUpdate`,
`lemListCatMaybes`, `lemListMapi`, `lemListInit`, `lemListZipSameLength`,
`lemListUnfoldr`, `lemInsertBy`, `lemStringConcat`, `lemShowListAux`);
library reps repointed (list.lem, list_extra.lem, sorting.lem, show.lem,
string.lem). Theorems (`lean-lib/LemLibTheorems.lean`, built with the
library; verbatim `#print axioms` lines):

```
'LemLibTheorems.lemListZip_eq' depends on axioms: [propext]
'LemLibTheorems.lemListUnzip_eq' depends on axioms: [propext]
'LemLibTheorems.lemListFoldr_eq' depends on axioms: [propext, Quot.sound]
'LemLibTheorems.lemListDeleteFirst_eq' depends on axioms: [propext, Quot.sound]
'LemLibTheorems.lemListUpdate_eq' depends on axioms: [propext]
'LemLibTheorems.lemListCatMaybes_eq' depends on axioms: [propext]
'LemLibTheorems.lemListMapi_eq' depends on axioms: [propext]
'LemLibTheorems.lemListInit_eq' depends on axioms: [propext]
'LemLibTheorems.lemListZipSameLength_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'LemLibTheorems.lemInsertBy_eq' depends on axioms: [propext]
'LemLibTheorems.lemStringConcat_eq' depends on axioms: [propext, Quot.sound]
'LemLibTheorems.lemShowListAux_eq' depends on axioms: [propext, Quot.sound]
```

Each theorem equates the rewrite with the REPLACED definition restated
verbatim (`*Spec`; the core function for zip/unzip/foldr). Two honest
limits: `lemListZipSameLength_eq` holds on the success domain (equal
lengths) — on unequal lengths both definitions reach `failwithI` with
the same message but cannot be equated as values (the spec conses a
prefix onto the opaque failure); `lemListUnfoldr` replaces a `partial
def` — kernel-opaque on both sides, so no equality theorem is
expressible. DISPOSITION: a declared kernel-opaque boundary, TEMPORAL;
mover = a fuelled (or structural, if a bound is found in the model) lem
`List_extra.unfoldr` that makes a theorem stateable; the two-target
parity run (p_list_deep `genlist`/`unfoldr`-free rows; the library
probe sweep) is the witness until then. Cerberus does not use
`List_extra.unfoldr` (it has its own fuelled `list_unfoldr`,
`frontend/model/utils.lem:295-359`).
Red (verbatim): `< zip: 300000 … > Stack overflow detected. Aborting.`
(23 rows lost). Green (verbatim): `=== p_list_deep === / OK: parity (28
lines byte-identical to the OCaml reference; pin matches)`.

### F3 / F10 / K1 — map insert semantics, iteration order, set order (DISCREPANCIES) — the Pset/Pmap port

Reference (`ocaml-lib/pmap.ml:67-73`): `Pmap.add` replaces a
comparator-equal binding storing the NEW key and datum; `Pmap.equal`
(`:253-261`, wrapper `:296`) compares keys with the MAP's comparator and
ignores lem's `eq_k`; `bindings`/`fold` ascend (`:152-156, :269-273`);
`Pset.add` (`pset.ml:76-80`) keeps the existing element; `Pset.elements`/
`fold` ascend; `union`'s surviving representative depends on subtree
HEIGHTS (`:168-183`); `set_case`/`choose_and_split` see the tree shape.
Because shape-dependent observables cannot be approximated, the two
AVL modules are ported line for line into LemLib (`Pset`, `Pmap`; every
function cites its source line; height-fuelled where the OCaml recursion
is not structural, with the loud `fuelExhaustedWith` sentinel), and
lem `set 'a` is now `Pset 'a`, `map` is `Fmap = empty | mk cmp Pmap`
(the comparator captured at first insert, as pmap.ml's `{cmp; m}`,
needed by `fmapEqualBy`; `empty` keeps the `lean_box(0)` ABI). New Lean
reps mirror the remaining OCaml reps exactly (`filter`, `mapBy`,
`bigunionBy`, `bigunionMapBy`, `crossBy`, `findMin`/`findMax`,
`toOrderedList`, `Map.toSetBy`); `Sorting.sort` is `sortByOrd compare`
on Lean as on OCaml (stable merge sort on both). The `transitiveClosureByEq`
Lean rep is dropped (no OCaml rep exists either: unbound on both).

Red (verbatim, p_map_beq): `< m1 toList: [(K(1,a), 1)] / > m1 toList:
[(K(1,a), 1); (K(1,b), 2)]`, `< m1 domain: [K(1,a)] / > … [K(1,b)]`,
`< m1 = m2 (mapEqual): true / > false`, `< m1 fold sum: 1 / > 3`;
p_show: `< {1; 2; 3} / > {3; 1; 2}`. Green (verbatim): `=== p_map_beq
=== / OK: parity (12 lines …)`, `=== p_show === / OK: parity (23 lines
…)`, new `=== p_set_ops === / OK: parity (39 lines …)` (union
representatives in both orders and for small-into-big / big-into-small,
map/bigunion/filter representatives, choose, findMin/Max, set_case,
chooseAndSplit root, sigma/cross, tc, show), `=== p_map_ops === / OK:
parity (25 lines …)` (insert replaces key+value, union both orders,
equality by comparator, domain/range representatives, map/mapi,
fromSet, toSet). `lean-lib/LemLibTest.lean` rewritten: AVL invariants
(well-formed heights, strict ascending traversal, cardinal, membership,
self-equality) over 8000 set and 5832 map operation sequences with
adversarial keys, plus kernel-checked (`decide`) examples of the OCaml
observables.

Consumer impact: `set 'a` is no longer `List α` — hand-written cerberus
Lean assuming the list representation breaks at compile time (loud;
convert with `setToList`/`setFromListBy`); set/map iteration order in
every printed output moves TOWARD the oracle; `lean_box(0)` remains the
empty map/set; the m10 `setSigmaBy`-ignores-comparator and
`chooseAndSplit` items are discharged by the port.

### F2 — strings are bytes (DISCREPANCY, L) — DESIGN ONLY in this slice

`doc/lean-backend/2026-09-03_string-representation-design.md`: the exact
OCaml semantics, why the only faithful route is a ByteArray-backed
`LemString`/`UInt8` char with every rep redirected and the backend's
literal emission changed (re-mapping Lean `String` is IMPOSSIBLE: a
non-UTF-8 byte string has no `String` value), consumer seams, the
parity probes that gate it, price L, slice plan. `p_str_bytes`,
`p_str_escapes` are registered expected failures (`expected_failures.txt`)
until the implementation slice; a runtime-refusal fallback is offered
only as an EXCEPTION-CASE for the operator.

### F9 — quadratic genlist / sort (ODDITY, performance) — registered

TODO.md item 7. `Sorting.sort` on Lean is now `sortByOrd compare`
(mergeSort) like OCaml; OCaml's quadratic `genlist` is an upstream
(non-Lean) change and stays registered.

## 2. Divergence census

Accepted exception classes (provenance [USER 2026-09-03], relayed by the
orchestrator): (a) failure-path MESSAGE TEXT — failure-vs-success must
agree per program, the text may differ; (b) RESOURCE LIMITS — Lean must
not fail where OCaml succeeds, the converse is acceptable; (c) MISSING
FEATURES — a loud, construct-naming GENERATION-TIME refusal is not a
divergence; a runtime-computed different result or silent absorption
is. Dispositions: FIX (with parity test) or EXCEPTION-CASE (argued for
the operator; NOT decided here). Sources swept: the noodle record,
LemLib in-code divergence notes, quality-review m10, the L1 deviations,
DESIGN.md/manual limitations, and LemLib against ocaml-lib module by
module (`.parity-scratch` rep-pair census over every `declare
ocaml`/`declare lean` pair of the library — the pair list itself is
reproduced by `awk` over library/*.lem, not committed).

| # | Item | Source | OCaml behaviour | Lean behaviour (pre) | Disposition | Evidence |
|---|---|---|---|---|---|---|
| F1 | int/int32/int64 div, mod | noodle F1 | Nat_num.int_div/int_mod | Euclidean | FIX | p_num_div green; test_integer_div F1 asserts |
| N3 | int32/int64 overflow | manual limitation | wrap (Int32/Int64) | unbounded Int | FIX | p_int_wrap green; f_int32_overflow |
| D1 | division by zero (all numeric types, mword) | m10 | raises Division_by_zero | 0 | FIX (class-(a) direction: Lean succeeded) | f_div_zero, f_int_div_zero, f_integer_mod_zero |
| N5 | integerSqrt of a negative | rep census | Z.sqrt raises | root of \|n\| | FIX | f_sqrt_neg |
| N6 | integerOfString / naturalOfString grammar | rep census | Z.of_string (sign, 0x/0o/0b, `_`, "" = 0; invalid → raise; negative natural → assert) | decimal only / `String.toNat?` | FIX | p_num_parse; f_num_parse_invalid; f_natural_neg |
| N4 | `nat`/`int` are 63-bit machine ints on OCaml | rep census (`type nat = int`; `to_int` raises Failure "int_of_big_int" at 2^62, `max_int + 1` wraps to -4611686018427387904, `abs min_int` = min_int) | wrap / raise past 2^62 | unbounded Nat/Int | CONVERSIONS FIXED (class-(a) shape: natFromNatural/natFromNumeral/intFromInteger/intFromNumeral fail loudly outside [-2^62, 2^62-1]); the arithmetic WRAP stays the EXCEPTION-CASE (§4, X3) pending the ruling | f_int_of_big_num; measured `t.ml` |
| F4 | derived Ord rank, single variants | noodle F4 | nullary below block | declaration index | FIX | p_cmp_order green; test_derived_comparison |
| F3 | Pmap.add / Pmap.equal semantics | noodle F3 | replace key+value; keys by comparator | bucket coexistence; eq_k | FIX (port) | p_map_beq, p_map_ops green |
| F10 | map iteration order | noodle F10 | ascending | newest-first | FIX (port) | p_map_ops rows toList/fold |
| K1 | set iteration/show order | LemLib.lean:300-305 (was "deliberate divergence") | ascending | insertion-derived | FIX (port) | p_show, p_set_ops green |
| S1 | union/map/bigunion/filter representatives; set_case; chooseAndSplit | pset.ml shape dependence | tree-shape dependent | list-based | FIX (verbatim port) | p_set_ops rows `union rep …`, `chooseAndSplit …`, `set_case` |
| S2 | setSigmaBy ignored its comparator; chooseAndSplit dropped EQ | m10 | Pset.sigma / root split | — | FIX (port) | p_set_ops `sigma`, `chooseAndSplit` |
| S3 | Set.findMin/findMax unbound on Lean | probe (F4 extension) | min_elt_opt/max_elt_opt | unbound (type error) | FIX (support) | p_set_ops `findMin/findMax` |
| S4 | Sorting.sort quadratic & unstable-order insertion sort | noodle F9 | List.sort (stable merge) | insertSortBy | FIX (same rep) + F9 registered | p_list_deep `sort`, p_set_ops `toOrderedList` |
| S5 | toOrderedList = sort (toList) by Ord vs Pset.elements by comparator | rep census | elements | sort | FIX (same rep) | p_set_ops |
| S6 | transitiveClosureByEq Lean rep with no OCaml counterpart | rep census | unbound | set_tc (BEq-keyed) | FIX → unbound on both (c) | manual |
| F6 | evaluation order of multi-draw expressions | noodle F6 | right-to-left (per node) | left-to-right | FIX | p_eval_order, p_supply_shapes green |
| L4 | supply-lifted top-level VALUE bindings | L1 deviation 4 | once at init | per use | FIX → generation-time REFUSAL (c) | neg_supply_toplevel_value |
| L5 | target_rep'd defs excluded from lifting | L1 deviation 5 | rep author's claim | same | not a backend divergence — kept | DESIGN.md |
| L3 | `natural` accepted by G-type | L1 deviation 3 | — | — | not behavioural — kept | — |
| F5 | draw under rep'd constructor refused | noodle F5 | evaluates | refusal (misdescribed) | FIX (support) | p_eval_order `just`; p_supply_shapes `mk_just` |
| F8 | Lean tokens/root names as top-level defs | noodle F8 | valid OCaml | invalid Lean | FIX | p_keywords green |
| F7 | 15 list/string functions overflow at 300k | noodle F7 + sweep | computes | stack overflow | FIX (b) | p_list_deep green; 12 theorems |
| R1 | closed-term extraction lifted failure sites to module init | found by f_div_zero | fails at the program point | silent init panic, default value | FIX (`never_extract`) | f_* probes |
| X2 | Debug.print_string/print_endline | debug.lem `let ~{ocaml} … = ()` | prints to stdout | no-op | FIXED via class-(c) GENERATION-TIME refusal (the `LemUnsupported.` marker hook; the audit showed the first attempt — a Unit-valued runtime failwithI — was dead-code-eliminated: `let u = Debug.print_endline "dbg" in …` printed nothing, exit 0) | negative/neg_unsupported_debug_print.lem |
| V1 | Vector.slice out of range | LemLib "PAD-WITH-DEFAULT, deliberately" | Array.sub raises | default padding | FIX (guard) | statically unreachable on both; no probe |
| F2 | strings/chars are bytes | noodle F2 | bytes | Unicode scalars | FIX scheduled (L; design note) | p_str_bytes, p_str_escapes XFAIL |
| X1 | polymorphic compare on values containing sets/maps | pset.ml/pmap.ml records carry a comparator closure | `compare` raises `Invalid_argument "compare: functional value"` (unless physically equal closures); `=` raises | structural comparison of the element spines | EXCEPTION-CASE candidate (§4) | reading; not probed |
| X4 | rational / real / float64 / float32 | LemLib "unsupported" panics | computes (Rational, float) | runtime panic on any use | FIXED via class-(c) GENERATION-TIME refusal (types and value entry points marked `LemUnsupported.`); whether `real`/`float64` should instead be supported on Lean `Float` stays an operator question (§4) | negative/neg_unsupported_rational.lem, neg_unsupported_real_entry.lem; cerberus uses none in `frontend/model` (grep) |
| X5 | `THE` (Hilbert choice) | function_extra | no OCaml definition (comment only) | runtime panic | unbound/unusable on both — no divergence | — |
| K2 | panic-then-default vs exception; List_extra.nth/head/last/nth out of range; naturalOfString invalid; `fromJust Nothing`; `failwith` | noodle K2 | raises | failwithI (panic + default; abort under harness) | EXCEPTION-ACCEPTED (a) | f_* probes exercise the both-fail rule |
| B1 | LemLib fuel sentinels (`fuelExhaustedWith`) in the ported set ops | port | OCaml recursion is unbounded; may loop (`lfp`) | bounded with loud sentinel | EXCEPTION-ACCEPTED (b) (Lean fails only where OCaml would not terminate or exceed the proven height bound) | port header |
| F9 | genlist quadratic on OCaml | noodle F9 | O(n²) | O(n) | performance — TODO #7 | — |

Derived totals (after the audit response): 31 rows; FIX 25 (incl. 5
class-(c) generation-time refusals — L4, S6, X2, X4, and the F4 unsupported-
head refusal — and 1 scheduled L); EXCEPTION-CASE candidates for the
operator 2 (N4 arithmetic wrap, X1); EXCEPTION-ACCEPTED under (a)/(b) 2
(K2, B1); not-a-divergence 3 (L5, L3, X5); performance 1 (F9). (Before
the audit: X2 and X4 were wrongly counted as fixed-at-runtime / candidate;
see the addendum.)

## 3. Close-out battery

### 3.1 tests/comprehensive `make lean` (final tree)

Old (bc1bae7, verbatim): `=== Generation: 47 passed, 0 failed, 0 skipped
===`, 6 compiled phases OK (panic, tuple-once, div-parity, supply-draws,
reader-consumer, fuel-budget), 41 negative probes `OK (rejected as
declared)`, 3 invariance files OK; no parity phase.

New (final tree; `make lean` exit 0): generation 47/47 (+2 joint),
compile green, 5 compiled phases OK (the M2 scaffold retired), 42
negative probes OK (41 + `neg_supply_toplevel_value`), 3 invariance
files OK, parity phase: 29 probes = 20 `OK: parity` + 7 `OK: both fail`
(failure probes) + 2 `XFAIL (expected, registered)` (F2). Verbatim lines
in §3.5.

### 3.2 `make nonlean-regress`

First run after the fixes drifted in 4 SEMANTIC artifacts
(`lib/{coq,hol,isa,ocaml}/lem_num.*`): the cause was the COMMENT text I
had changed on two `declare lean target_rep type int32/int64` lines
(lem echoes source comments into every backend's output). Comments
restored → semantic emitters (ocaml, hol, isa, coq) byte-identical
(verbatim: the drift list filtered to those emitters is empty). The
remaining drift is confined to the ECHO targets (`lem`, `ident`, `tex`,
`html`, `tex_all`): they re-render the library SOURCE, and the source
gained Lean-scoped declares (`declare lean target_rep …`, `{ocaml;lean}`
target sets) — `git diff bc1bae7 -- library/*.lem` is exactly that
delta (Lean-scoped lines only, plus the restored comments). Per the
net's protocol the goldens are rebaselined
(`NONLEAN_REGRESS_REBASELINE=1`) in the commit that carries the library
edits; the semantic emitters' rows are unchanged in the manifest.

### 3.3 Corpus tree-diff vs bc1bae7

bc1bae7's `tests/comprehensive/test_*.lem` generated with the bc1bae7
lem+library and with the final lem+library (`.parity-scratch/corpus-{old,new}`):
11 of 92 files differ, plus `test_supply.lem` no longer generates on the
new lem (its `let (top_a, top_b) = pair_draw ()` is the deviation-4
refusal; the committed test was updated). Every differing file
classified: F4 derived ranks replace `deriving BEq, Ord` on mixed-order
variants (Test_case_arm_parsing, Test_derived_comparison, Test_deriving,
Test_types_advanced); `set 'a` is `Pset` (Test_collections,
Test_instances — also `Set.map` via `setMapBy` —, Test_misc); division
reps `lemNatDiv`/`lemNatMod`/`lemIntegerDiv` replace `/`/`%`
(Test_either_maybe, Test_integer_div, Test_numeric, Test_termination).
No other pure emission changed; supply-threaded emission changes only
in test_supply (F5/F6, by design).

### 3.4 lean-lib

`lake build` green: LemLib (with the ports and rewrites), LemLibTest
(8000 + 5832 sequences under `#guard`, kernel `decide` examples),
LemLibTheorems (12 theorems, axioms listed under F7).

### 3.5 Final verbatim gate lines

`tests/comprehensive`, `make lean` (final tree), verbatim:

```
=== Generation: 47 passed, 0 failed, 0 skipped ===
  OK: test_cross_recup_base.lem + test_cross_recup_import.lem (joint)
  OK: test_cross_field_access.lem + test_cross_field_access_import.lem (joint)
  OK (leg 1): panic prints the Incomplete Pattern message, then continues with default
  OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1
  OK: draws: first=1 second=2
  OK: compiled draw sequences hold
  OK: compiled consumer injection holds
  OK: budgeted cut at 5; unannotated at the exact lemDefaultFuel boundary
  OK: inv_fuel_budget.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_reader_consumer.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_supply.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
```

(42 `OK (rejected as declared)` negative-probe lines; derived count.)
Parity phase, verbatim `OK` lines (derived count 20 + 7; the two XFAIL
probes print their diff and `XFAIL (expected, registered): F2 …`):

```
=== f_div_zero === / OK: both fail (lean exit 134: PANIC at _private.LemLib.0.failwithIImpl LemLib:158:2: Division_by_zero …); stdout prefix identical (2 lines)
=== f_int32_overflow === / OK: both fail (… Nat_big_num.to_int32: Overflow (2147483648) …); stdout prefix identical (1 lines)
=== f_int_div_zero === / OK: both fail (… Division_by_zero …); stdout prefix identical (1 lines)
=== f_integer_mod_zero === / OK: both fail (… Division_by_zero …); stdout prefix identical (1 lines)
=== f_natural_neg === / OK: both fail (… Assertion failed (Nat_big_num.of_string_nat: negative) …); stdout prefix identical (1 lines)
=== f_num_parse_invalid === / OK: both fail (… Z.of_substring_base: invalid digit …); stdout prefix identical (1 lines)
=== f_sqrt_neg === / OK: both fail (… Z.sqrt: square root of a negative number …); stdout prefix identical (1 lines)
=== p_cmp_order === / OK: parity (45 lines byte-identical to the OCaml reference; pin matches)
=== p_eval_order === / OK: parity (21 lines …)
=== p_functions === / OK: parity (21 lines …)
=== p_hello === / OK: parity (3 lines …)
=== p_int_wrap === / OK: parity (42 lines …)
=== p_keywords === / OK: parity (91 lines …)
=== p_list_deep === / OK: parity (28 lines …)
=== p_list_ops === / OK: parity (31 lines …)
=== p_map_beq === / OK: parity (12 lines …)
=== p_map_ops === / OK: parity (25 lines …)
=== p_monad === / OK: parity (8 lines …)
=== p_num_div === / OK: parity (11 lines …)
=== p_num_misc === / OK: parity (42 lines …)
=== p_num_parse === / OK: parity (29 lines …)
=== p_patterns === / OK: parity (16 lines …)
=== p_precedence === / OK: parity (44 lines …)
=== p_records === / OK: parity (23 lines …)
=== p_set_ops === / OK: parity (39 lines …)
=== p_show === / OK: parity (23 lines …)
=== p_str_bytes === / XFAIL (expected, registered): F2 strings-are-bytes — design note …
=== p_str_escapes === / XFAIL (expected, registered): F2 strings-are-bytes (unicode literal row) …
=== p_supply_shapes === / OK: parity (35 lines …)
```

`make nonlean-regress` (final tree, after the echo-target rebaseline of
§3.2), verbatim: `nonlean-regress: OK (893 artifact rows, 216 exit rows,
9 emitters, byte-identical to golden)`.

`lean-lib`: `lake build` — `Build completed successfully (37 jobs).`

Note on commits: the brief asked for one commit per finding on green;
the fixes share files (`src/lean_backend.ml` carries F4, F5, F6, F8;
`lean-lib/LemLib.lean` carries F1, N3, D1, F7, the Pset/Pmap port and
the census fixes), and intermediate per-finding trees were not
individually gated, so the slice lands as five logical commits
(infrastructure; backend; library; suite tests; docs), each stating that
the gates above were run on the FINAL tree.

## 4. EXCEPTION-CASE arguments for the operator (not decided here)

> RULED 2026-09-03 ([USER] agreed with the lem framing): X1 and X3/N4 are recorded as
> OCaml-backend deviations from lem's own prover-side semantics — the Lean
> target follows lem; not exceptions. X2/X4 were fixed as class-(c)
> generation-time refusals in this same commit. Record:
> `2026-09-03_exception-case-rulings.md`. The arguments below are kept
> verbatim as the record of what was asked.

**X3 / N4 — OCaml `nat`/`int` are 63-bit machine integers.** lem `nat`
is OCaml `int` (`num.lem:117`), lem `int` is OCaml `int`; `natFromNatural`,
`intFromInteger`, `natFromNumeral` are `Nat_big_num.to_int` which raises
`Failure "int_of_big_int"` at 2^62 (measured verbatim: `2^62 -> EXN
Failure("int_of_big_int")`, `2^62-1 -> 4611686018427387903`), while
`+`/`*`/`abs` WRAP silently (`maxint+1 -> -4611686018427387904`, `abs
minint -> -4611686018427387904`). Lean's `Nat`/`Int` are unbounded. For:
mirroring requires modular arithmetic on every `nat`/`int` operation
(a cost on the hottest paths, and a semantic model of a runtime quirk
that is wrong for the mathematics the specs mean) and loud failure in
the conversions; reachability needs values ≥ 2^62 ≈ 4.6·10^18 — beyond
any list length, index or counter — and cerberus keeps its C-semantic
arithmetic in `integer` (Z). Against: it is a difference in computed
results, not a failure-text or resource matter, so no accepted class
covers it. Proposed rule: accept as an exception ("machine-integer
overflow of lem `nat`/`int` on the OCaml target is not mirrored; the
Lean value is the mathematical one"), OR fix the conversions only
(loud failure at ≥ 2^62, S) and accept the arithmetic wrap.

**X1 — polymorphic compare on values that contain a set or map.** OCaml
`compare`/`=` on a Pset/Pmap value (a record with a comparator closure)
raises `Invalid_argument "compare: functional value"` (except `compare`
on physically identical closures), so lem's derived equality on a type
with a set field FAILS on the OCaml target; Lean's structural instances
compute. This is Lean succeeding where OCaml raises. For an exception:
the OCaml behaviour is a runtime accident of the closure representation,
not a semantics anyone specified, and cerberus's own equalities on such
types go through lem's `setEqual`/`mapEqual` (comparator-keyed on both);
mirroring would mean panicking in derived instances that consumers may
rely on. Against: the rule says Lean must fail where OCaml fails. Not
probed (a probe would need a cerberus-shaped type); proposed rule:
accept, with an in-code note at the `BEq`/`Ord (Pset α)` instances (in
place).

**X2 — `Debug.print_string`/`print_endline` (generation-time form).**
Fixed here as a loud runtime refusal (previously a silent no-op, a
divergence). The (c) form would refuse at GENERATION time; lem's
`compile_message` declare is a warning, not an error, and a per-target
error hook does not exist in the backend today. Proposed: accept the
runtime refusal as the (c) equivalent for this construct, or fund a
per-target "unsupported constant" error in the backend (S) and route
`Debug.*`, and `rational`/`real`/`float*` (X4), through it.

**X4 — `rational`, `real`, `float64`, `float32`.** Panic on any use on
Lean; OCaml computes (Rational, float). Cerberus's `frontend/model` uses
none of them (grep). Lean has `Float` (IEEE double), so `real`/`float64`
COULD be supported (S/M, incl. `string_of_float` formatting parity);
`rational` needs a rational library. Proposed: (c) generation-time
refusal (with the X2 hook) unless the operator wants the Float support.

## 5. Consumer-impact summary for the cerberus pin bump (separate slice)

Read-only greps of `cerberus-lean/lean_frontend` (hand-written seams and
`generated/`), audit-response 2026-09-03:

- **Removed LemLib names** and where cerberus references them:
  `fmapOfSpine` — `Main.lean` (4 call sites, :696-702; the union of
  spine lists must become `fmapAddBy` folds or a `Pmap`-typed build) and
  its `generated/Main.lean` copy. NOT referenced anywhere in cerberus:
  `fromNat32`, `fromNat64`, `lemCmpToOrd`, `LemInt32`, `lemInt32Abs`,
  `lemInt32ToNat`, `LemInt64`, `lemInt64Abs`, `set_tc`, `set_tc_go`,
  `sortedCompareBy`, `toNat32`, `toNat64`.
- **Pset-typed sites** (`set 'a` is `Pset α`, no longer `List α`):
  `CerbCall.lean:77` (`setToList (Lem_Set.filter …)` — still valid, the
  list is produced by `setToList`; the ARGUMENT set is now a `Pset`);
  `CerbFunMapInstances.lean:15-25` — the "PHANTOM requirement" comment
  describes `Lem_Map_extra.fold` as `setFold … (fmapElements m)`: stale
  (`fold` is now `Set_helpers.fold` over `Map.toSet` = `Pset.fold`,
  ascending), rewrite the comment; `CerbUtils.lean:59-61` `set_fold`
  ("Lem sets are sorted lists via LemSet … foldl") is dead and its
  premise false — delete. Generated uses of `setToList`/`setFromListBy`/
  `setAddBy`/`setMemberBy` (Cmm_op, Cmm_csem, Core_linking, Core_run,
  Utils, Driver, Cabs_to_ail_effect, Translation_aux, Core_typing,
  Cn_desugaring, Defacto_memory) regenerate with the new types.
- **Division-by-zero panic sites**: the generated `Defacto_memory_aux.lean`
  (7 lines with `/` or `%`, derived count) and `CerbMem.lean` (22) now
  render through `lemNatDiv`/`lemIntegerDiv`/… and PANIC on a zero
  divisor where the OCaml oracle raises. The hand-written guard
  `CerbMem.lean:1352` `if n2 == 0 then 0 else integerDiv_t n1 n2` returns
  0 where the oracle RAISES `Division_by_zero`: a cerberus-side
  divergence for the zero-discrepancy census — flagged, not fixed here.
- **Renames (F8 + the audit's rename-scope fix)**: NO cerberus generated
  ROOT definition is newly renamed by the extended `lean_constants` (the
  13 root defs renamed at bc1bae7 — `attribute0`, `break0`, `catch0`,
  `get0`, `guard0`, `liftM0`, `mapM0`, `modify0`, `namespace0`,
  `prefix0`, `return0`, `run0`, `throw0` — stay renamed; the only
  NEW-list hit, `main`, is the hand-written entry point). Constructors
  KEEP the avoidance (see §6 F2: dropping it made every pattern on an
  exported constructor that shadows a root constant ambiguous), so the
  17 constructors renamed at bc1bae7 (`Add0 And0 Div0 Mod0 Mul0 Ne0 Or0
  Sub0` in AilSyntax, `Array0 Float0 Union0 Void0` in Ctype, `Bool0
  Char0` in IntegerType, `Dynamic0 Neg0` in Core, `One0` in Cmm_csem)
  are UNCHANGED at the pin bump. Record fields no longer avoid the list:
  the field `Core.main` keeps its name (`Main.lean:562`, `CerbCall.lean:9`
  keep compiling) and the one field renamed at bc1bae7, `Utils.default0`,
  changes back to `default` (a hand-written reference to `default0`
  would break loudly).
- **Generation-time refusals** newly possible at the bump: `Debug.print_*`
  and `rational`/`real`/`float64`/`float32` uses (none in
  `frontend/model`, grep); a mixed-order variant self-referential under
  an unsupported head (none found by the scan).

- F4: 35 mixed-order variants change instance shape (derived
  `compare_derived`); order moves toward the oracle in `Set.choose`,
  `topo_order`, sorts. Differential battery is the gate.
- F6/F5: multi-draw expressions renumber (right-to-left); id-canonical
  lanes unaffected; the uri diagnostic row (C1-F2) re-records.
- Pset/Pmap: `set 'a` is `Pset`, not `List` — hand-written seams that
  pattern-match lists break loudly; iteration order ascending
  everywhere; `lean_box(0)` ABI kept.
- Numbers: `int32`/`int64` types are `Int32`/`Int64` (unused by
  cerberus); division by zero panics (any unguarded site that relied
  on `x / 0 = 0` now panics — the OCaml oracle raises there, so the
  battery decides); `natDiv`/`natMod`/`integerDiv`/`integerMod` render
  as `lemNatDiv` etc.
- F8: renamed generated names for 213 more root identifiers.
- F7: `List.foldr`/`zip`/`unzip` and the listed library functions
  render as their `lem*` rewrites.
- LemLib API removals: the list-based set functions, `set_tc`, the
  `Std.TreeMap` Fmap internals, `LemInt32`/`LemInt64`.


## 6. Audit-response addendum (2026-09-03)

Fresh audit verdict: MERGE-SAFE-WITH-NOTES, two HIGH record-integrity
items + notes; one audit-response commit follows this addendum.

**F1 (HIGH) — census row X2 was FALSE.** The audit's probe `let u =
Debug.print_endline "dbg" in match u with () -> "after"` printed `dbg` on
OCaml and NOTHING on Lean (exit 0, no PANIC): the `Unit`-valued
`failwithI` was dead-code-eliminated (`never_extract` prevents
closed-term extraction, not DCE). FIX: the class-(c) GENERATION-TIME
refusal — the `LemUnsupported.` marker protocol (DESIGN.md; backend
`lean_unsupported_check_cref`/`_type` at every constant-reference and
type-annotation site outside library modules). Routed through it:
`Debug.print_string`/`print_endline`, and the X4 family — the types
`rational`/`real`/`float64`/`float32` and their value entry points
`rationalFromNumeral/FromInt/FromInteger/FromFrac`,
`realFromNumeral/FromInteger/FromFrac`. Red → green, verbatim: the
bc1bae7 lem ACCEPTED the probe (exit 0; emitted `def  probe   (u  : Unit)
:  String :=  let  u  := Lem_Debug.print_endline  "dbg";  match  u with |
() =>  "after"`); the fixed lem: `Error: Lean backend: constant
'Debug.print_endline' has no implementation on the Lean target (its
library rep is the unsupported marker 'LemUnsupported.debugPrintEndline';
the OCaml reference implements it) — this use is REFUSED at generation
time: remove it, or give the enclosing definition a Lean target_rep`
(exit 1). Negative probes `neg_unsupported_debug_print`,
`neg_unsupported_rational` (type leg), `neg_unsupported_real_entry` all
`OK (rejected as declared)`. Census rows X2/X4, the manual, DESIGN.md and
TODO #8 corrected/registered. Sizing: S (backend ~60 lines, one marker
namespace in LemLib, rep edits).

**F2 (HIGH) — the F8 rename also renamed record fields and constructors.**
`rename_top_level.ml` applied `get_fresh_name` against the reserved list
to every shown constant; the cerberus field `Core.main` would have become
`main0`. The orchestrator's decision [AGENT, orchestrator,
operator-overridable] was to restrict the avoidance to ROOT-namespace
constants for both fields and constructors, with the instruction to
VERIFY the no-clash claim. VERIFIED, with a split result: (i) a
stand-alone probe — `inductive T | Sep | One` + `export T (Sep One)`,
`structure R where main : Nat; mt : Bool` + `open R`, uses `Sep 1`,
`One`, `main r`, `mt r` — compiles on Lean 4.28.0 (exit 0), so
EXPRESSIONS resolve by expected type; but (ii) applying the restriction
to constructors made the parity corpus FAIL to build, verbatim:
`P_eval_order.lean:151:9: ambiguous pattern, use fully qualified name,
possible interpretations [_root_.One, two.One]` and `P_records.lean:316:90:
ambiguous pattern … [_root_.Add, expr.Add]`, `… [_root_.Seq, stmt.Seq]`
— PATTERNS on an exported constructor that shadows a root constant are
ambiguous (loud, but every such generated file breaks). Disposition
[AGENT]: fields drop the root-constant avoidance (the cerberus case,
`Core.main`), constructors keep it exactly as at bc1bae7 (so `Add0`,
`One0`, … do not move at the pin bump); the alternative — emitting
fully-qualified constructor patterns — is a larger backend change and
is registered for the operator. Corpus tree-diff and cerberus
enumeration: §3.3 and §5 (updated).

**F4 — consumer-note omissions** filled in §5 (removed names with
referencing files; Pset-typed sites; division-by-zero panic sites and
the `CerbMem.lean:1352` cerberus-side divergence flag).

**N4/X3 conversions (FIX, class-(a) shape).** `natFromNatural`,
`intFromInteger` (the `Nat_big_num.to_int` reps) fail loudly outside the
OCaml 63-bit range where the reference raises `Failure
"int_of_big_int"`; failure probe `f_int_of_big_num` — verbatim: `OK: both
fail (lean exit 134: PANIC at … Failure "int_of_big_int"
(4611686018427387904 outside the OCaml 6…); stdout prefix identical (2
lines)`. `natFromNumeral`/`intFromNumeral` keep the literal-passthrough
reps: a lem numeral is emitted as a literal on both targets (a literal
≥ 2^62 is an OCaml compile error — folded into the N4 exception row).
The arithmetic wrap stays the EXCEPTION-CASE pending the ruling.

**Record precision (F5/F6/F7):** F6 record-field sentence corrected
(labels sorted to declaration order, then right-to-left — last-declared
first); F6's red reproducible only on the pre-F5 rows (stated); F4 tally
criterion stated, `GenTypes.genType` added; `lemListUnfoldr` disposition
recorded as a TEMPORAL kernel-opaque boundary with its mover; the
comprehensive Makefile's six `lake build` invocations run through
`$(CAPPED)` (fail-noisy `check-capped` target) with the runner's
`CERB_MEM_MAX`.

Close-out battery after the response (final tree), verbatim:
`=== Generation: 47 passed, 0 failed, 0 skipped ===`; compile green; the
5 compiled phases OK; 45 `OK (rejected as declared)` (42 +
`neg_unsupported_debug_print`, `neg_unsupported_rational`,
`neg_unsupported_real_entry`); 3 invariance OK; parity 20 `OK: parity` +
8 `OK: both fail` (+ `f_int_of_big_num`) + 2 XFAIL (F2); `make lean`
exit 0. `nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)`. `lean-lib` `lake build`: `Build completed successfully (37
jobs).` Corpus tree-diff (bc1bae7 sources, bc1bae7 lem vs final lem):
13 of 92 files, the SAME set as §3.3 (11 files + `test_supply.lem`'s
value-binding refusal) — the rename-scope change alters no file of the
corpus (no record field of the bc1bae7 tests is named like a Lean root
constant; the `Empty0`/`map0` identifiers in the diffs are constructor/def
names present on BOTH sides), and the constructor renames are unchanged
by design (F2 above).
