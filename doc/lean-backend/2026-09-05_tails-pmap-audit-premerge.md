# Pre-merge audit — `arc/tails-and-pmap-laws` (lem-lean), 2026-09-05

Auditor [AGENT], independent of the slice's worker. Range audited:
`ecf75b4` (mainline `mdd/lean-backend`) → `a30b0bc` (branch head; 3
commits: `b10b574` the emission-side tails rule, `80e7dfe` the `Pmap`
laws, `a30b0bc` the record). Worktree
`worktrees/lem-lean-audit/tails-pmap-premerge` (branch
`audit/tails-pmap-premerge` @ `a30b0bc`), fresh `make` of lem there;
baseline lem rebuilt from `git archive ecf75b4` (`.tmp/lem-base`,
`make exit 0`). Nothing merged, nothing pushed; cerberus-lean read-only
(`git archive` of `753644005` into `.tmp/cerb`). Every quoted output
below is verbatim from this worktree (`.tmp/*.log`, `.tmp/probes/`);
tallies marked "derived" are derived. Findings are claims: each carries
its measurement.

## Verdict

**MERGEABLE (ff-only) with one MINOR fix recommended before or
immediately after merge (F1), the rest MINOR/NOTE.** No non-Lean emitter
change, no `.lem` change, no change to the Lean output of any existing
definition (cerberus tree 170/170 files byte-identical, suite 52
pre-existing modules 104/104 files byte-identical), no axiom/`sorry`, no
option bump, kernel-only proofs, laws stated as the consumer asked. The
one real hole found (F1) is a capture through a user-authored
`target_rep` naming the synthesized binder; it is a PRE-EXISTING class
(the same probe captures `lemFuel` at `ecf75b4`), the new code's hygiene
check is in fact stricter than the existing reserved-binder scan, and
the fix is one clause. Graded MINOR for those reasons — the scope's
literal MAJOR wording ("a hygiene hole (capture/shadowing)") covers it,
so the operator may overrule the grade.

## Findings

### MAJOR — none.

### MINOR

**F1 (MINOR; MAJOR by the scope's literal wording — operator's call).
Capture through a Lean `target_rep` equal to `lemTail` is not refused;
demonstrated as a well-typed OCaml/Lean discrepancy.** The hygiene check
(`lean_hoist_tail_binders`, `body_consts`) compares `lemTail` against
the LEM name of every constant the body references
(`Path.get_name … const_binding`), not against the Lean text the
constant renders as. Probe `.tmp/probes/p11b_target_rep_lemTail_silent.lem`:

```lem
val dl : list nat
let dl = []
declare lean target_rep function dl = `lemTail`
val bad : nat -> list nat -> nat
let rec bad acc = function | [] -> acc | _ :: xs -> bad (acc + 1) (if acc = 0 then dl else xs) end
declare {lean} fuel val bad = `fun _ => acc`
declare {lean} fuel_measure val bad = `List.length lemTail + 1`
```

accepted (`exit 0`); generated worker arm, verbatim:
`| Nat.succ lemFuel => ( match lemTail with  |  [] =>  acc |  _  ::  xs => (bad_lemFuel lemFuel)  (acc  +   1)  (if  acc  ==   0 then  lemTail  else  xs) )`
— `dl` became the hoisted binder. Compiled against LemLib and evaluated
(`lake env lean`, `#eval bad 0 [1, 2, 3]`): Lean prints `4`; the OCaml
target (`ocamlfind ocamlopt`, same `.lem`) prints `1`. A silent
behavioural discrepancy, contrary to the record's "hygiene, fail-closed".
Mitigation of the grade, measured: the identical hole exists at
`ecf75b4` for the reserved binder `lemFuel` —
`.tmp/probes/p11c_target_rep_lemFuel_preexisting.lem` (`declare lean
target_rep function seven = `lemFuel`` in a fuel'd def) is accepted by
the BASE lem, worker verbatim `| Nat.succ lemFuel => ( if  n  ==   0
then  lemFuel  else (g_lemFuel lemFuel)  (n  -   1))` — the existing
`reserved_binder_check` (lean_backend.ml:4268) scans binders only, not
constant reps at all; the tails check at least scans referenced
constants' lem names. Trigger requires an author to write a `target_rep`
equal to a documented synthesized name. **Fix (one clause + one
negative probe):** in `lean_hoist_tail_binders`, also compare against
the Lean `target_rep` string of every referenced constant (the same
lookup the emitter uses for `Constant` rendering), and — since the class
is shared — do the same for `lemFuel`/`lemMeasureLe`/`_lemReader_`/
`_lemSupply` in `reserved_binder_check` (separate slice; registered
here for TODO). Not a blocker for this range because it does not
regress `ecf75b4`.

**F2 (MINOR). No generic `CmpLaws` bridge; every consumer key type
needs a hand proof.** The only instance shipped is
`Pmap.cmpLaws_defaultCompare_nat`. The consumer's Core environments
insert with the literal lambda `(fun (sym1 : sym) (sym2 : sym)=>
ordCompare  sym1  sym2)` (verbatim from `Core_aux.lean:636/654` at
`753644005`), i.e. cerberus's hand-written `instance (Ord sym)`
(symbol.lem:169: digest compare, then `nat` compare). That comparator is
provably a strict weak order — `CerberusFresh.digest_compare` is a Lean
`def` on `String` (CerberusFresh.lean:43), not an opaque extern — but
the proof is the consumer's, per key type. Lean core's `Std.TransCmp`
/`Std.OrientedCmp` (with `cmp_congr_left/right`) give `refl`/`flip`/
`lt_trans`/`eq_congr` for `defaultCompare` uniformly over any lawful
`Ord`; a `theorem cmpLaws_defaultCompare_of_TransCmp [Ord α] [Std.TransCmp
(compare : α → α → Ordering)] : CmpLaws (defaultCompare : α → α → LemOrdering)`
would cover `Nat`/`Int`/`String` keys at once. Derived comparators
(`compare_derived`, lexicographic with the OCaml constructor rank, leaf
fields via `Ord.compare`) satisfy `CmpLaws` iff their leaf `Ord`s do —
also per-type work today. The record states the gap honestly (decision
1); it is a gap all the same. S.

**F3 (MINOR, documentation precision).** The rule as IMPLEMENTED hoists
any trailing lambda whose binders are plain variables for a
measured/structural definition, with or without a `function` beneath it.
Probe `.tmp/probes/p13_measured_user_fun_no_function.lem` (`let rec f n
= fun k -> if n = 0 then k else f (n - 1) (k + 1)`, measure `n + 1`):
at `ecf75b4` the worker is `f_lemFuel (lemFuel : Nat) (n : Nat) : Nat →
Nat` with a `fun (k : Nat) =>` body and the wrapper `def f (n : Nat) :
Nat → Nat`; at `a30b0bc` it is `f_lemFuel … (n : Nat) (k : Nat) : Nat`
and `def f (n : Nat) (k : Nat) : Nat` — a consumer-visible ARITY change
for such a definition (extensionally equal; the `_zero` lemma becomes
`((fun _ => 0) k)`). The record/manual describe the user lambda only as
sitting "above" a `function`. Measured impact on cerberus: none — the
Lean tree at `753644005` without the new declares is byte-identical
under both lems (170/170, below), so no existing measured row has this
shape. Fix: either state the rule as implemented ("every trailing
lambda of a measured/structural clause body") in DESIGN/manual/record,
or gate the hoist on a `remove_function` lambda being present. NOTE-
grade behaviour, MINOR-grade because the manual's statement is what a
cerberus author will rely on.

### NOTE

**N1.** The dry run's "modules differing before/after" list in the record
(the two declared modules, their auxiliaries, and the callers
`Ctype_aux`, `GenTypesAux`, `GenTyping`, `Cabs_to_ail*`, `Mini_pipeline`)
is confirmed: 13 modules differ (`AilTypesAux(+_auxiliary)`,
`Core_reduction(+_auxiliary)`, `Cabs_to_ail_aux`, `Cabs_to_ail_effect`,
`Cabs_to_ail`, `Ctype_aux`, `GenTypesAux`, `GenTyping`, `Mini_pipeline`,
plus `Cmm_csem`/`Cmm_op` whose diff is ONLY the source path embedded in
lem's non-exhaustive-match failure strings — an artifact of my
`frontend-after/` copy, 32/32 and 4/4 differing lines mention the path).

**N2.** `Fmap.WF cmp (.mk c m)` pins `c = cmp` (decision 2). For the
consumer this is `rfl`: every generated insertion site rebuilds the same
lambda, and `(fun s1 s2 => ordCompare s1 s2) = ordCompare` is
definitional (eta). No action.

**N3.** `eq_congr` is independent of `refl`/`flip`/`lt_trans` as the
file claims: three keys with `a ~ b`, `b ~ c`, `a < c` satisfy the
other three (no `LT`–`LT` chain exists) and violate `eq_congr`. The
hypothesis is honest and minimal for a replace-on-EQ map; `find?_add_same`
uses only `refl` at the list level but needs `WF_add` (all four) for the
tree-to-list step — bundling is right.

**N4.** The `body_free` clause of the hygiene check is unreachable in
practice (a top-level clause body's free variables are its parameters,
caught first by the parameter check; lem has no local `let rec`);
harmless. The `body_consts` check is conservative by design: a record
FIELD named `lemTail` referenced as `r.lemTail` is refused
(`.tmp/probes/p14`), which is fine (fail-closed, message names the
remedy).

**N5.** The Lean BUILD of the dry-run cerberus tree was not attempted
(nor by the record; scope = accept + generate). In particular the
`_zero` lemma of `one_step_unseq_aux` (implicit `{a b : Type}`) is now
fully applied, so the fuel-measure record §2.4 ascription problem
cannot recur there by construction, but this is by reading, not by
build. The cerberus half will build it.

**N6.** Record §2.6 / decision 3: the shared-counter measures for the
two mutual blocks are acceptance witnesses only — confirmed as the
record's own caveat, and correct: `List.length lemTail + 1` cannot bound
a `get_ctx_unseq_aux` step that recurses into a deep `get_ctx`; the
joint measure is the cerberus half's.

**N7.** Provenance: the record marks the worker `[AGENT]` and quotes the
one ruling with `[USER 2026-09-04]`; the five §7 decisions are under a
heading "Decisions for the operator" without per-item `[AGENT]` tags.
Acceptable under the record's preamble; per-item tags would remove any
doubt. Commit `b10b574`'s message tallies (`53 generated, 160 jobs`;
`893/216/9`; `86/86, diff 0 lines`) match my re-run exactly.

## 1. TAILS — measurements

**Gating.** `lean_hoist_tail_binders` (lean_backend.ml:3015) matches a
single-clause group only `when … (fuel_measure_for c <> None ||
is_structural_cref c)`, outside comments and instances; applied once at
the `Fun_def` branch before de-mutualization/fuel plan/structural
analysis (`:3928`). Discriminator for the compiler's lambda is the locn
tag `Ast.Trans (_, "remove_function", _)`, which is the macro's own mark
(patterns.ml:1670 `Ast.Trans(true, "remove_function", Some …)`, the
`Fun` and its `Case`/`Var`/`pvar` all carry `l_unk`). Supply refusal is
meaningful: `St.supply_lifted` is filled by `lean_supply_prepass`
(`:2470`) before any def renders. Sentinel application:
`fuel_sentinel_output` emits `((payload) <hoisted…>)` when
`St.tail_sentinel_args` is non-empty, set/restored around the fuel'd
group's render (`:4390`/`:4409`).

**Byte-identity of everything not declared (my measurement, beyond the
record's).**
- The 52 pre-existing `tests/comprehensive/test_*.lem` (incl. the two
  joint pairs), generated with the `ecf75b4` lem and the `a30b0bc` lem:
  `LEAN TEST-MODULE DIFF (ecf75b4 lem vs a30b0bc lem, 52 sources) exit 0 lines 0`
  (104 `.lean` files each side; 6 of the sources carry
  `fuel_measure`/`structural`).
- The cerberus Lean tree (`frontend/` @ `753644005`, cerberus flags,
  `LEM_SRC_LEAN` = 85 files, no new declares), both lems:
  `LEAN DIFF (base lem vs new lem, no new declares) exit 0 lines 0`
  (170 files each).
- Probe `p15` (plain fuel'd tail + undeclared tail): `IDENTICAL`.

**Probes (`.tmp/probes/`, all with the `a30b0bc` lem; `.tmp/probes.log`).**

| # | Probe | Result (verbatim reason where refused) |
|---|---|---|
| p01 | `lemTail` as a user parameter | REFUSED: `… would shadow a parameter of the same name — rename that variable` |
| p02 | body binder `let lemTail = …` in an arm | REFUSED: `… would collide with a binder of the same name in the body` |
| p03 | top-level constant `lemTail` referenced in the body | REFUSED: `… would capture a constant of the same name referenced in the body` |
| p04 | top-level constant `lemTail` NOT referenced | ACCEPTED (`exit 0`; base lem refuses `structural` here as before — the definition previously "met the existing refusals") |
| p05 | `fun acc -> function …` shadowing parameter `acc` | REFUSED: `hoisting the binder `acc` of the trailing lambda into the head would shadow a parameter of the same name` |
| p06 | `let rec bad (a, b) = fun a -> function …` | REFUSED: `hoisting the binder `a` … would capture it by the destructuring pattern of a parameter it sits under` |
| p07 | `function` tail under a `let` in the body (measured) | NOT hoisted; refused downstream: `free variable `lemTail` in the fuel measure of f (FM-free …)` |
| p07b | same, `structural` | NOT hoisted; refused by the structural analysis (`no parameter of f is passed a strict structural subterm`) |
| p08 | supply-lifted def with a tail | REFUSED: `eta-expansion of a supply-lifted definition (unsupported: the supply prepass threads call sites at the pre-hoist arity; extend when needed)` |
| p09 | user-written `fun x -> match x with …` | ACCEPTED, binder kept as `x`: `def f_lemFuel (lemFuel : Nat) (acc : Nat) (x : List (Nat)) : Nat`, wrapper `def f ( acc : Nat) ( x : List (Nat))`; no `lemTail` in the file — the tag is the discriminator |
| p10 | `fun _ -> function …` (wildcard) | NOT hoisted; refused downstream (FM-free) |
| p11 | constant with `target_rep … = `lemTail`` referenced (Nat-typed) | ACCEPTED — generated `[] => acc + lemTail` (a Lean type error downstream: loud) |
| p11b | same, list-typed | ACCEPTED — **silent discrepancy, F1** (Lean `4`, OCaml `1`) |
| p11c | `target_rep … = `lemFuel`` in a fuel'd def, BASE lem | ACCEPTED at `ecf75b4` — pre-existing class |
| p12 | `fun lemTail -> function …` (user binder named lemTail) | REFUSED: `… would shadow a parameter of the same name` (the user binder was hoisted first, then the scrutinee binder clashed) |
| p13 | measured `fun k ->` with no `function` | ACCEPTED, `k` hoisted — F3 |
| p14 | record field `lemTail` projected in the body | REFUSED (conservative, `capture a constant of the same name`) |
| p15 | plain fuel'd tail + undeclared tail | byte-identical to `ecf75b4` |
| p17 | two destructuring parameters `(a, b) (c, d) = function …` | ACCEPTED: `def f_lemFuel (lemFuel : Nat) (p : (Nat ×Nat)) (p0 : (Nat ×Nat)) (lemTail : List (Nat)) : Nat`; wrapper `f (p) (p0) (lemTail)` |

**Sentinel typing and `_zero` = `rfl`.** The suite compiled
`Test_function_tails.lean` (`Build completed successfully (160 jobs)`);
generated verbatim: `theorem tlen_lemFuel_zero ( acc : Nat) (lemTail :
List (Nat)) :` / `tlen_lemFuel 0  acc lemTail = ((fun _ => acc) lemTail)
:= rfl`; the un-hoisted `plain_tail` keeps
`(plain_tail_lemFuel 0  acc : List (Nat) → Nat) = (fun _ => acc) := rfl`
and `def plain_tail [LemFuel]`. `TestFunctionTailsCheck.lean` pins
`decide`/`rfl` through every wrapper, the applied sentinel, and
`funext`-recovers the point-free lemma; `#print axioms` of `slen_eq`/
`sscale_eq` in the suite transcript.

**Invariance and the net.**
`  OK: inv_function_tails.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)`;
`nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)`
(`.tmp/nonlean-1.log`, 2:15 wall).

## 2. LAWS — `lean-lib/LemLibPmapLaws.lean` (read in full)

(a) `CmpLaws` — see N3/F2. `flip` is stated as an equation on the
three-valued result (`cmp b a = match cmp a b with …`), which gives
`eq_symm`, `lt_gt`, `gt_lt` and, with `eq_congr`, the right congruence
— exactly the OCaml `Map` contract under a total preorder `compare`.
`compare_derived` (lean_backend.ml:7756: lexicographic `cmp_chain`, leaf
`Ord.compare`, fallback `Ord.compare (ctor_rank_ocaml …)`) is a strict
weak order whenever its leaf `Ord`s are — no generic instance ships (F2).

(b) `Pmap.WF cmp m := (toList m).Pairwise (fun a b => cmp a.1 b.1 = .LT)`,
decidable (`infer_instance`). Replace-on-EQ preserved: `toList_add`'s
EQ arm rewrites through `insertList_append_gt` (everything left of the
node is GT of the new key by `gt_of_eq_of_gt`) and then the `insertList`
EQ step, so the new key replaces the old binding in place;
`insertList_pairwise` EQ arm re-establishes the bound with
`lt_of_eq_of_lt`. `bal`: `toList_bal` is proved with no invariant —
`unfold bal; repeat' split; … first | simp … | exfalso; omega` — the
four `failwithI "Map.bal"` arms are closed by `omega` on the heights
(`height Empty = 0` cannot exceed `hr + 2`). No `sorry`/`admit`/
`native_decide`/`bv_decide`/`ofReduce`/`set_option`/`axiom` token in the
file (grep: only the doc comment mentions the words); `grep -c "^axiom "`
over every `lean-lib/*.lean` and `LemLib/*.lean`: all 0. `decide` is used
only on the closed four-binding pins and on `LemOrdering` literals.

(c) Statements match the consumer's §1 shapes exactly:
`find?_add_same : … find? cmp k (add cmp k v m) = some v`,
`find?_add_other : … cmp k k' ≠ .EQ → find? cmp k (add cmp k' v m) = find? cmp k m`,
both under `CmpLaws cmp` and `WF cmp m` (the "whatever well-formedness
predicate they need" — `WF_Empty` and `WF_add` give it for `fmapEmpty`
and every `fmapAddBy`: yes, `Fmap.WF_empty : WF cmp .empty` is `trivial`
and `Fmap.WF_fmapAddBy` preserves it given `CmpLaws`). `Fmap`
corollaries take an arbitrary `c'` for `fmapLookupBy` (it ignores its
comparator, as pmap.ml's wrapper does). The consumer wrote "strict total
order"; the delivered hypothesis is weaker (strict weak order) — fine
(decision 1). `#print axioms`, re-run (`.tmp/leanlib-build.log`):

```
info: LemLibPmapLaws.lean:475:0: 'Pmap.find?_add_same' depends on axioms: [propext, Quot.sound]
info: LemLibPmapLaws.lean:476:0: 'Pmap.find?_add_other' depends on axioms: [propext, Quot.sound]
info: LemLibPmapLaws.lean:477:0: 'Pmap.WF_add' depends on axioms: [propext, Quot.sound]
info: LemLibPmapLaws.lean:478:0: 'Fmap.fmapLookupBy_fmapAddBy_same' depends on axioms: [propext, Quot.sound]
info: LemLibPmapLaws.lean:479:0: 'Fmap.fmapLookupBy_fmapAddBy_other' depends on axioms: [propext, Quot.sound]
info: LemLibPmapLaws.lean:480:0: 'Pmap.cmpLaws_defaultCompare_nat' depends on axioms: [propext, Quot.sound]
Build completed successfully (39 jobs).
```

Build time of the file: `ℹ [38/39] Built LemLibPmapLaws (1.5s)` (the
other 38 jobs replayed from the suite's build of the path dependency;
whole `lake build` 2.0s wall). Lean 4.28.0, capped 16G.

## 3. THE CERBERUS DRY RUN (`.tmp/cerb/run.sh`, `.tmp/cerb-dryrun.log`)

`frontend/` from `git archive 753644005` (93 `.lem`), cerberus's flags
(`-wl ign -wl_rename warn -wl_pat_red err -wl_pat_exh warn -cerberus_pp`),
`LEM_SRC` 86 / `LEM_SRC_LEAN` 85 read from cerberus's Makefile; the six
declares appended exactly as the record lists them (`core_reduction.lem`:
`one_step_unseq_aux = `List.length lemTail + 1``, `get_ctx = `lemSize g +
1``, `get_ctx_unseq_aux = `List.length lemTail + 1``; `ail/ailTypesAux.lem`:
`are_compatible = `ctype.lemSize p.2 + ctype.lemSize p0.2 + 1``,
`are_compatible_params_aux = `List.length lemTail.1 + 1``,
`are_compatible_params = `List.length params1 + 1``). Verbatim:

```
base ocaml exit 0
new ocaml exit 0
files: base=86 new=86
OCAML DIFF exit 0 lines 0
base lean exit 0 files 170
new lean(before) exit 0 files 170
LEAN DIFF (base lem vs new lem, no new declares) exit 0 lines 0
new lean(after) exit 0 files 170
--- [LemFuel] binder count before/after (derived): 397 -> 351
```

Six of six accepted; wrapper heads byte-identical to the record's table
(e.g. `def are_compatible_params_aux (acc : Bool) (lemTail : (List
((qualifiers ×ctype ×Bool)) ×List ((qualifiers ×ctype ×Bool)))) : Bool :=
are_compatible_params_aux_lemFuel (List.length lemTail.1 + 1) acc lemTail`);
obligations: 3 theorems in `Core_reduction_auxiliary.lean`
(`one_step_unseq_aux_`, `get_ctx_`, `get_ctx_unseq_aux_measure_sufficient`)
and 3 in `AilTypesAux_auxiliary.lean`. Differing modules modulo the
path header: N1. The record's caveat that the shared-counter measures
are acceptance witnesses only is noted and agreed (N6). `lean-after.log`
carries only the pre-existing non-exhaustive-match warnings
(`cmm_op.lem`, `cmm_csem.lem`).

## 4. NON-LEAN BLAST RADIUS

`nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)`
— no rebaseline in the range (`golden.*` untouched in the diff stat).
Cerberus OCaml tree, `ecf75b4` lem vs `a30b0bc` lem (§3):
`files: base=86 new=86` / `OCAML DIFF exit 0 lines 0`. `git diff --stat
ecf75b4..a30b0bc`: 19 files, only `src/lean_backend.ml` under `src/`
(no `.lem`, no other backend, no parser/typechecker).

## 5. RECORD

Tallies: `397 → 351` `[LemFuel]` binders reproduced (derived, same
method); `53 passed, 0 failed, 0 skipped`; `160 jobs`; `39 jobs`;
`893/216/9`; `86/86`; `170` files; `11 lines` parity pin; `7 artifacts`
— all reproduced. TODO row 17 marked RESOLVED with the original text
kept; row 19 opened as DELIVERED with the unrequested follow-ups
(`Pset`, `remove`, `bindings = toList`) listed. Provenance: N7. The
before/after `tlen` diff in §2.4 of the record matches the generated
`Test_function_tails.lean` heads verbatim.

## 6. Gates re-run here (verbatim, `.tmp/suite-1.log`)

```
=== Generation: 53 passed, 0 failed, 0 skipped ===
Build completed successfully (160 jobs).
  OK (leg 1): panic prints the Incomplete Pattern message, then continues with default
  OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1
single-evaluation: OK
  OK: compiled draw sequences hold
  OK: compiled consumer injection holds
  OK (leg 1): two sufficient fuels agree; insufficient gives the declared sentinel; callee starts from the full ambient
  OK (leg 2): loud exhaustion at an insufficient runtime fuel fail-stops (exit 134)
  OK (rejected as declared): negative/neg_tail_body_binder.lem
  OK (rejected as declared): negative/neg_tail_shadow_param.lem
  OK (rejected as declared): negative/neg_tail_user_shadow.lem
  OK: inv_function_tails.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
=== p_function_tails ===
  OK: parity (11 lines byte-identical to the OCaml reference; pin matches)
  OK: 8 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
  OK: 248 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make lean  402.50s user 53.07s system 123% cpu 6:09.75 total
exit 0
```

The four `FAIL` lines in the parity phase are the four registered
XFAILs (`p_str_bytes`, `p_str_escapes`, `f_int_of_big_num`,
`f_int32_overflow`), each followed by its `XFAIL (expected, registered)`
line — unchanged from `ecf75b4`. No run exceeded 10 minutes (longest:
the suite, 6:10).

## 7. Not checked

- The Lean BUILD of the dry-run cerberus tree with the six declares
  (N5; out of scope for both the record and this audit).
- The `ecf75b4`-vs-`a30b0bc` byte-identity of the HOL/Isabelle/Coq
  outputs of the cerberus tree specifically (the net's 893-row golden
  over the library + `tests/backends` corpus and the invariance witness
  stand in; the tails code is confined to `lean_backend.ml`, so the
  emitters cannot differ).
- Constructor names colliding with `lemTail` (lem constructors are
  rendered qualified; not probed).
- `Pset`/`remove`/`bindings` laws (unrequested, TODO 19).
