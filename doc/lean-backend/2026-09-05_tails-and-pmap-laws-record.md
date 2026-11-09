# Tails-and-Pmap-laws slice — record (2026-09-05)

Branch `arc/tails-and-pmap-laws` (lem-lean), from mainline `mdd/lean-backend`
@ `ecf75b4`. Charter: TODO row 17 (point-free `function` tails) as a
Lean-only emission fix, and the consumer's `Pmap` lookup-after-insert laws
(refined-cerberus `docs/2026-09-03_request-lem-lean-pmap-laws-and-fuel-scheme.md`
§1). Worker [AGENT] (lem-lean); rulings quoted with [USER] provenance;
every quoted output is verbatim from this worktree (`.tmp/` logs named);
tallies marked "derived" are derived. Nothing merged, nothing pushed;
cerberus-lean read-only (the dry run is on a scratch copy).

## 0. Commits

| Commit | Content |
|---|---|
| `b10b574` | point-free `function` tails: the emission-side eta-expansion (`lean_hoist_tail_binders`, `St.tail_hoisted`/`tail_sentinel_args`, the applied sentinel); tests (`test_function_tails.lem` + proofs + kernel pins, 3 negatives, invariance witness, parity probe + proofs + pin); manual, DESIGN, TODO row 17 |
| `80e7dfe` | `lean-lib/LemLibPmapLaws.lean` (the `Pmap`/`Fmap` laws, kernel-only) + lakefile root + lean-lib README; TODO row 19 |
| this commit | this record |

## 1. The rulings this slice implements

[USER 2026-09-04] (fuel-measure record §1): keeping to the principle that
the lem structure is not changed for OCaml's sake is a good design rule
— so the seven census rows whose recursion
argument is an anonymous `function` scrutinee are NOT eta-expanded in the
`.lem` (the row-17 option (1)); the LEAN EMISSION is. The brief's rules,
all met: no magic values, zero axioms, kernel-only proofs (no
`native_decide`/`bv_decide`, no heartbeat bump — none was needed), the
OCaml output byte-identical, the non-Lean emitters untouched.

## 2. Point-free `function` tails (TODO 17)

### 2.1 The problem, precisely

`let rec f acc = function | [] -> … | x :: xs -> f (acc + 1) xs`. lem's
pattern compiler (`Patterns.remove_function`, Lean target) turns the
`function` into `fun x -> match x with …` with a fresh `x`, so the clause
body is a lambda: the head binds ONE parameter (`acc`) while the val type
has two arrows. Both Lean-only termination mechanisms range over the
head's parameters — `lean_structural_assign` designates a parameter by
position, `lean_render_measure` accepts only parameter names — so neither
can name the list. Cerberus census rows 37, 39, 40, 64, 65, 66 (fuel-measure
record §6.2) were RESIDUE for exactly this reason (row 39 `get_ctx` and 64
`are_compatible` via a mutual sibling: all-or-none).

### 2.2 The rule (two sentences)

For a definition that carries `declare {lean} fuel_measure val` or
`declare {lean} structural val` (and only those — every other definition
renders as before), the Lean emission hoists EVERY trailing lambda with
plain-variable binders of the clause body into the head: the binder the
pattern compiler made for a `function` becomes the deterministic name
`lemTail` (its match scrutinee renamed with it), a user-written `fun k
->` — above a `function` or on its own (audit F3, probe `p13`) — keeps
the user's name, and the hoist goes through a `Paren` and through the
single-arm match the compiler emits for a destructuring parameter (`let
rec f (a, b) = function …` ↦ `match p with | (a, b) => fun x => …`). The head's result
annotation loses one arrow per hoisted binder, the fuel sentinel — written
in the `.lem` at the head's ORIGINAL function-typed codomain — is applied
to the hoisted binders in the worker's exhaustion arm and the `_zero`
lemma (`((payload) lemTail)`, the same value by β), and the OCaml/HOL/
Isabelle/Coq emitters never see any of it.

Implementation: `src/lean_backend.ml` `lean_hoist_tail_binders` (functor
level, after `is_structural_cref`; mechanism comment there), applied to
every clause group right after `lean_group_funcls` in the `Fun_def`
branch — BEFORE the demutualization, the fuel plan, the structural
analysis and the measured wrapper read the clause parameters; two `St`
fields (`tail_hoisted` [file], `tail_sentinel_args` [render], both on
the reset hooks); `fuel_sentinel_output` applies the payload when
`tail_sentinel_args` is non-empty. Detection of the compiler's lambda is
by its location tag `Ast.Trans (_, "remove_function", _)` (the macro's
own mark), never by shape — a user-written `fun x -> match x with …` is
hoisted under the user's `x`.

### 2.3 Why one binder, why this name, what else was considered

- **One fresh binder per `function`, every user binder as is** — the
  scrutinee is the only binder the compiler invented; everything else in
  the tail is the user's (a `fun k ->`, hoisted under `k`; `fun a b ->`
  hoists both), and the rule applies to a trailing user lambda WITHOUT a
  `function` beneath it just the same (audit F3: `let rec f n = fun k ->
  …` measured becomes `def f (n : Nat) (k : Nat) : Nat` — a
  consumer-visible arity change for such a definition, extensionally the
  same function, the point-free form recovered by `funext`; the
  alternative — gating on the `remove_function` tag — was not taken: the
  general rule is simpler to state, is what a measure over `k` would
  need, and has zero cerberus impact, the tree being byte-identical
  without the new declares). A wildcard lambda binder (`fun _ ->`) is not
  hoisted (no name to give it short of inventing a second synthesized
  name); the definition then meets the existing refusals.
- **Why `lemTail` and not the macro's `x`**: `Name.fresh (r"x")` yields
  `x`, `x1`, … depending on which names are FREE in the body — a measure
  in the `.lem` must name the binder, and an author cannot see the macro's
  choice. A fixed name is deterministic from the `.lem` alone. It joins
  the backend's synthesized names (`lemFuel`, `lemMeasureLe`,
  `_lemReader_*`, `_lemSupply*`) but is checked LOCALLY (only where a
  hoist happens), not added to the global reserved-binder scan — a
  fuel'd definition without a tail may use the name freely (decision 4
  for the operator, §7).
- **Hygiene, fail-closed** (the brief: "refused if it would shadow"):
  `lemTail` is refused when it is a head parameter, a binder anywhere in
  the clause body (`exp_bound_names`), a free variable of the body, or
  the lem name of a constant the body references
  (`neg_tail_shadow_param`, `neg_tail_body_binder`); a hoisted user
  binder is refused when it would shadow a parameter or be captured by
  the destructuring pattern it is hoisted through (`neg_tail_user_shadow`).
  Hoisting a supply-lifted definition is refused (the supply prepass
  threads call sites at the pre-hoist arity — extend when needed).
- **Alternatives not taken**: (a) eta-expanding the `.lem` — the ruling;
  (b) a measure syntax naming tail argument POSITIONS with the wrapper
  eta-expanding (row 17's "backend alternative") — new declare vocabulary
  under the consolidation freeze (TODO 18), and it leaves `structural`
  blind (the structural analysis needs a parameter, not a position);
  (c) hoisting for EVERY fuel'd definition — changes the (B)-class
  point-free workers (`liftAction`, `plain_tail`) for no benefit; the
  brief asked for the generated Lean to be otherwise unchanged, and the
  fuel-measure slice's codomain-ascribed `_zero` lemma stays the shape of
  an un-measured tail (pinned).

### 2.4 Before / after — one function, verbatim

`tlen` (`test_function_tails.lem` (a)), with `fuel` only (before) and with
`fuel` + `fuel_measure` (after); `diff` of the two generated modules
(`.tmp/tails-before-after-fuel.diff`):

```
28,30c28,30
<  def  tlen_lemFuel (lemFuel : Nat)  (acc : Nat)  : List (Nat) → Nat := match lemFuel with
<   | 0 => (fun _ => acc)
<   | Nat.succ lemFuel => ( fun (x : List (Nat)) =>  match x with  |  [] =>  acc |  _  ::  xs => (tlen_lemFuel lemFuel)  (acc  +   1)  xs
---
>  def  tlen_lemFuel (lemFuel : Nat)  (acc : Nat) (lemTail : List (Nat))  : Nat := match lemFuel with
>   | 0 => ((fun _ => acc) lemTail)
>   | Nat.succ lemFuel => ( match lemTail with  |  [] =>  acc |  _  ::  xs => (tlen_lemFuel lemFuel)  (acc  +   1)  xs
33,35c33,35
< def tlen [LemFuel] : Nat → List (Nat) → Nat := tlen_lemFuel LemFuel.fuel
< theorem tlen_lemFuel_zero ( acc : Nat) :
<     (tlen_lemFuel 0  acc : List (Nat) → Nat) = (fun _ => acc) := rfl
---
> def tlen ( acc : Nat) (lemTail : List (Nat)) : Nat := tlen_lemFuel (List.length lemTail + 1)  acc lemTail
> theorem tlen_lemFuel_zero ( acc : Nat) (lemTail : List (Nat)) :
>     tlen_lemFuel 0  acc lemTail = ((fun _ => acc) lemTail) := rfl
```

The same function without any declare (before) vs `structural` (after)
(`.tmp/tails-before-after-structural.diff`):

```
28c28,30
<  partial def  slen  (acc : Nat)  : List (Nat) → Nat :=  fun (x : List (Nat)) =>  match x with  |  [] =>  acc |  _  ::  xs =>  slen  (acc  +   1)  xs
---
>  def  slen  (acc : Nat) (lemTail : List (Nat))  : Nat :=  match lemTail with  |  [] =>  acc |  _  ::  xs =>  slen  (acc  +   1)  xs
> 
> termination_by structural lemTail
```

The destructuring-parameter shape (cerberus `one_step_unseq_aux`),
generated worker (`Test_function_tails.lean`, `tpair`):

```lean
 def  tpair_lemFuel (lemFuel : Nat)  (p : (Nat ×Nat)) (lemTail : List (Nat))  : (Nat ×Nat) := match lemFuel with
  | 0 => ((fun _ => (0, 0)) lemTail)
  | Nat.succ lemFuel => (match p with |  (a,  b) => ( match lemTail with  |  [] =>  (a, b) |  x  ::  xs => (tpair_lemFuel lemFuel)  ((a  +  x), (b  +   1))  xs ) )
```

### 2.5 Tests

- `tests/comprehensive/test_function_tails.lem` — the six cerberus shapes
  in miniature: (a) `let rec tlen acc = function …` measured over
  `lemTail`; (b) the same `structural` (`termination_by structural
  lemTail`); (c) `tpair (a, b) = function …` (the destructuring parameter,
  hoisted through the compiler's single-arm match); (d) `fun k -> function`
  (k and lemTail hoisted); (e) the truly mutual `tev`/`todd` (a
  named-parameter member and a tail member, `get_ctx`'s shape,
  all-or-none measures); (f) `tdot acc = function | ([], []) …` over a
  pair of lists, measure `List.length lemTail.1 + 1`
  (`are_compatible_params_aux`'s shape); (g) `structural` under `fun k ->
  function`; (h) `tuser n = fun k -> …` with no `function` (audit F3,
  probe `p13`: `k` hoisted, wrapper `def tuser (n : Nat) (k : Nat) : Nat`);
  and `plain_tail`, an ambient fuel'd tail that is NOT hoisted (the
  fuel-measure slice's codomain-ascribed `_zero` lemma, pinned). Ten lem
  asserts (measured/structural defs are fuel-free, so assertable).
- `lean-test/Test_function_tails_lemMeasureProofs.lean` — the six
  obligations (stability by induction on the hoisted list; `tdot` by
  destructuring the pair, `tev`/`todd` jointly); verbatim:
  `'Test_function_tails_lemMeasureProofs.tlen_measure_sufficient' depends on axioms: [propext, Quot.sound]`
  (and identically `tpair`, `tscale`, `tev`, `todd`, `tdot`).
- `lean-test/TestFunctionTailsCheck.lean` — kernel pins: `decide`/`rfl`
  through every wrapper and structural def; wrapper = worker at the
  measure over `lemTail` by `rfl`; fuel-free signatures; the `_zero`
  lemma applied to the hoisted binder (`tlen_lemFuel 0 acc l = acc` by
  β, the point-free form recovered by `funext`); the un-hoisted
  `plain_tail` shape; `slen_eq`/`sscale_eq` inductive proofs over the
  hoisted parameter (`[propext, Quot.sound]`).
- Negatives: `neg_tail_shadow_param.lem` (parameter named `lemTail`),
  `neg_tail_body_binder.lem` (a `let lemTail` in an arm),
  `neg_tail_user_shadow.lem` (`let rec bad acc = fun acc -> function …`),
  `neg_tail_rep_capture.lem` and `neg_fuel_rep_capture.lem` (a constant
  whose Lean `target_rep` is `lemTail` / `lemFuel` referenced in the body
  — audit F1, §8).
- Invariance: `invariance/inv_function_tails.lem` — the three declared
  shapes; `OK: inv_function_tails.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)`.
- Parity: `parity/probes/p_function_tails.lem` + `.proofs.lean`, pin
  `expected/p_function_tails.out` (11 lines, recorded with `REBASELINE=1`
  from the OCaml reference); `OK: parity (11 lines byte-identical to the OCaml reference; pin matches)`.

### 2.6 The cerberus dry run (read-only; `.tmp/cerb`, scratch copy of `frontend/` @ cerberus-lean mainline `753644005`)

Method: `frontend/` copied; the Lean tree generated with cerberus's
flags (`-wl ign -wl_rename warn -wl_pat_red err -wl_pat_exh warn
-cerberus_pp -lean`, `LEM_SRC_LEAN` = 85 files, `make --eval`) BEFORE
(`lean-before`, 170 files) and AFTER adding six `declare {lean}
fuel_measure val` lines (`lean-after`); the measures name the hoisted
binder where the row's recursion is the `function` argument, the derived
size elsewhere. Binder names read from the baseline tree's `_zero`
lemmas (`p`, `g`, `annot1 acc es1`, `p p0`, `acc`, `params1 params2`).
Generation: `lean-after exit 0 files 170`. Per row:

| Row (record §6.2) | Function | Measure declared | Result | Generated wrapper (verbatim head) |
|---|---|---|---|---|
| 37 | `one_step_unseq_aux` (core_reduction) | `List.length lemTail + 1` | ACCEPTED, generates | `def one_step_unseq_aux  {a : Type} {b : Type} (p : (List (dyn_annotation) ×List (value))) (lemTail : List (generic_expr b a (sym))) : Option ((List (dyn_annotation) ×List (value))) := one_step_unseq_aux_lemFuel (List.length lemTail + 1) p lemTail` |
| 39 | `get_ctx` (core_reduction; mutual with 40) | `lemSize g + 1` | ACCEPTED, generates | `def get_ctx (g : generic_expr (core_run_annotation) (Unit) (sym)) : List ((context ×expr (core_run_annotation))) := get_ctx_lemFuel (generic_expr.lemSize g + 1) g` |
| 40 | `get_ctx_unseq_aux` (core_reduction) | `List.length lemTail + 1` | ACCEPTED, generates | `def get_ctx_unseq_aux (annot1 : List (annot)) (acc : …) (es1 : …) (lemTail : List (generic_expr (core_run_annotation) (Unit) (sym))) : … := get_ctx_unseq_aux_lemFuel (List.length lemTail + 1) annot1 acc es1 lemTail` |
| 64 | `are_compatible` (ail/ailTypesAux; mutual with 65, 66) | `ctype.lemSize p.2 + ctype.lemSize p0.2 + 1` | ACCEPTED, generates | `def are_compatible (p : (qualifiers ×ctype)) (p0 : (qualifiers ×ctype)) : Bool := are_compatible_lemFuel (ctype.lemSize p.2 + ctype.lemSize p0.2 + 1) p p0` |
| 65 | `are_compatible_params_aux` (ail/ailTypesAux) | `List.length lemTail.1 + 1` | ACCEPTED, generates | `def are_compatible_params_aux (acc : Bool) (lemTail : (List ((qualifiers ×ctype ×Bool)) ×List ((qualifiers ×ctype ×Bool)))) : Bool := are_compatible_params_aux_lemFuel (List.length lemTail.1 + 1) acc lemTail` |
| 66 | `are_compatible_params` (ail/ailTypesAux) | `List.length params1 + 1` | ACCEPTED, generates | `def are_compatible_params (params1 : …) (params2 : …) : Bool := are_compatible_params_lemFuel (List.length params1 + 1) params1 params2` |

Six of six accepted (0 refused). Derived counts: `[LemFuel]` binders in
the tree 397 → 351 (the two blocks' callers — `Ctype_aux`, `GenTypesAux`,
`GenTyping`, `Cabs_to_ail*`, `Mini_pipeline` — lose the binder); the six
obligations land in `Core_reduction_auxiliary.lean` (3) and
`AilTypesAux_auxiliary.lean` (3). The Lean BUILD of the dry-run tree was
not attempted (scope: accept + generate; the sufficiency proofs are the
cerberus half's, and for the two SHARED-counter mutual blocks the
measures above are acceptance witnesses, not claimed-sufficient — §7
decision 3). The cerberus `.lem` was not edited.

### 2.7 OCaml byte-identity

`.tmp/cerb`: the copy WITHOUT the six declares, `LEM_SRC` = 86 files,
cerberus's flags, baseline lem = `ecf75b4` rebuilt from `git archive`
(`.tmp/lem-base`, `make build-lem`, `exit 0`), this lem = the worktree's;
verbatim:

```
base exit 0
new exit 0
files: base=86 new=86
OCAML DIFF exit 0 lines 0
```

(The copy WITH the declares cannot be parsed by the baseline — as for
every new `{lean}` declare; on the Lean side the only modules that
differ between `lean-before` and `lean-after` are the two declared
modules, their auxiliaries and the callers that lose `[LemFuel]`.)

## 3. `Pmap` laws for the consumer (`lean-lib/LemLibPmapLaws.lean`)

### 3.1 Statements (verbatim from the file)

```lean
structure Pmap.CmpLaws (cmp : α → α → LemOrdering) : Prop where
  refl : ∀ a, cmp a a = .EQ
  flip : ∀ a b, cmp b a = (match cmp a b with | .LT => .GT | .EQ => .EQ | .GT => .LT)
  lt_trans : ∀ a b c, cmp a b = .LT → cmp b c = .LT → cmp a c = .LT
  eq_congr : ∀ a b c, cmp a b = .EQ → cmp a c = cmp b c

def Pmap.toList : Pmap α β → List (α × β)          -- in-order bindings
def Pmap.WF (cmp : α → α → LemOrdering) (m : Pmap α β) : Prop :=
  (toList m).Pairwise (fun a b => cmp a.1 b.1 = .LT)   -- decidable instance provided

theorem Pmap.WF_Empty (cmp) : WF cmp (.Empty : Pmap α β)
theorem Pmap.WF_add (h : CmpLaws cmp) (k : α) (v : β) (m : Pmap α β) (hw : WF cmp m) : WF cmp (add cmp k v m)
theorem Pmap.find?_add_same (h : CmpLaws cmp) (k : α) (v : β) (m : Pmap α β) (hw : WF cmp m) :
    find? cmp k (add cmp k v m) = some v
theorem Pmap.find?_add_other (h : CmpLaws cmp) (k k' : α) (v : β) (m : Pmap α β) (hw : WF cmp m)
    (hne : cmp k k' ≠ .EQ) : find? cmp k (add cmp k' v m) = find? cmp k m

def Fmap.WF (cmp : α → α → LemOrdering) : Fmap α β → Prop
  | .empty => True
  | .mk c m => c = cmp ∧ Pmap.WF cmp m
theorem Fmap.WF_empty, Fmap.WF_fmapAddBy
theorem Fmap.fmapLookupBy_fmapAddBy_same (h : Pmap.CmpLaws cmp) (c' : α → α → LemOrdering) (k : α) (v : β)
    (m : Fmap α β) (hw : WF cmp m) : fmapLookupBy c' k (fmapAddBy cmp k v m) = some v
theorem Fmap.fmapLookupBy_fmapAddBy_other (h : Pmap.CmpLaws cmp) (c' : α → α → LemOrdering) (k k' : α) (v : β)
    (m : Fmap α β) (hw : WF cmp m) (hne : cmp k k' ≠ .EQ) :
    fmapLookupBy c' k (fmapAddBy cmp k' v m) = fmapLookupBy c' k m
theorem Pmap.cmpLaws_defaultCompare_nat : Pmap.CmpLaws (defaultCompare : Nat → Nat → LemOrdering)
-- audit response F2 (§8): the generic bridge from Lean core's lawful-Ord class
theorem Pmap.cmpLaws_of_transOrd {α : Type} [Ord α] [Std.TransOrd α] :
    Pmap.CmpLaws (defaultCompare : α → α → LemOrdering)
theorem Pmap.cmpLaws_defaultCompare_int / _string / _nat' := Pmap.cmpLaws_of_transOrd
```

`#print axioms`, verbatim (`lake build` in `lean-lib`):

```
'Pmap.find?_add_same' depends on axioms: [propext, Quot.sound]
'Pmap.find?_add_other' depends on axioms: [propext, Quot.sound]
'Pmap.WF_add' depends on axioms: [propext, Quot.sound]
'Fmap.fmapLookupBy_fmapAddBy_same' depends on axioms: [propext, Quot.sound]
'Fmap.fmapLookupBy_fmapAddBy_other' depends on axioms: [propext, Quot.sound]
'Pmap.cmpLaws_defaultCompare_nat' depends on axioms: [propext, Quot.sound]
```

### 3.2 The proof, and why the hypotheses are what they are

Route: everything through the in-order list. `toList_create` and
`toList_bal` (the AVL rotations are in-order-preserving rewrites: every
`create`/`bal` arm's `toList` is `toList l ++ (x, d) :: toList r` — the
four `failwithI "Map.bal"` arms are excluded by ARITHMETIC on the heights
alone: `height Empty = 0` cannot exceed `hr + 2`, and an `Empty` inner
child cannot have the greater height — no `heightsOk` needed; proof:
`unfold bal; repeat' split; simp only [height]; repeat' split; simp …
| exfalso; omega`). Then `toList (add cmp k v m) = insertList cmp k v
(toList m)` (sorted insert-or-replace) and `find? cmp k m = lookupList
cmp k (toList m)` under `WF`, both by induction on the tree using the
bounds `WF_node` reads off `List.pairwise_append`; then the two laws are
the list facts `lookupList k (insertList k v xs) = some v` (needs only
`refl`) and `cmp k k' ≠ EQ → lookupList k (insertList k' v xs) =
lookupList k xs` (needs right-congruence, derived from `eq_congr` +
`flip`). `WF_add` is `insertList` preserving `Pairwise` (`lt_trans`,
`flip`, `eq_congr`).

Where each law of `CmpLaws` is USED: `refl` — `find?` finds the key it
just stored (`Node l k v r h` at an EQ hit; `[(k, v)]` at a leaf);
`flip` — a key LT the node key is GT of it from the other side
(`insertList_append_gt`, the `Pairwise` bounds); `lt_trans` — a key below
the node key is below everything right of it; `eq_congr` — a key
comparator-EQ to another compares identically against a third, which is
what lets `find?` skip a whole subtree and what makes "replace the EQ
binding" sound. The consumer's phrase was "a strict total order";
`CmpLaws` is the weaker STRICT WEAK ORDER on the three-valued comparator
(EQ an equivalence compatible with LT), because that is exactly what
`Pmap.add`'s replace-on-EQ semantics (pmap.ml:67, storing the NEW key)
promises — the laws hold and are stated up to the comparator, as in
OCaml's `Map` under a total-preorder `compare`. Every strict total order
with decidable equality satisfies it (`cmpLaws_defaultCompare_nat`);
`eq_congr` is not derivable from the other three (decision 1, §7).

Unit pins (kernel, closed maps; `decide`/`rfl`): both laws on a
four-binding map (`m0`), the replaced-key case, `toList m0`,
`Pmap.WF cNat m0` by `decide` through the new `Decidable` instance, an
`Fmap` instance.

### 3.3 Not done (unrequested)

The same laws for `Pset` (`mem`/`add`), for `remove`, and the equation
`bindings m = toList m` (the accumulator form `bindingsAux`) — S each,
registered on TODO row 19.

## 4. Gates — verbatim

All from this worktree at the final tree (`.tmp/suite-1.log`,
`.tmp/nonlean-1.log`, the `lake build` transcript, `.tmp/cerb`).

`tests/comprehensive` `make lean` (Lean 4.28.0, `CERB_MEM_MAX=16G`, capped),
the phase verdicts verbatim:

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
  OK: parity (11 lines byte-identical to the OCaml reference; pin matches)
  OK: 8 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
  OK: 248 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make lean  317.64s user 25.72s system 94% cpu 6:04.58 total
exit 0
```

(all 79 negative probes and 7 invariance witnesses OK; the parity phase's
four `FAIL` lines are the four REGISTERED expected failures —
`p_str_bytes`, `p_str_escapes`, `f_int_of_big_num`, `f_int32_overflow` —
each followed by its `XFAIL (expected, registered)` line, unchanged from
`ecf75b4`.) The tails proofs module: `'Test_function_tails_lemMeasureProofs.tlen_measure_sufficient' depends on axioms: [propext, Quot.sound]` (the six theorems identical).

`lean-lib` `lake build` (39 jobs): `Build completed successfully (39 jobs).`
— the six `#print axioms` lines of §3.1 verbatim in the transcript; `grep
-c "^axiom " lean-lib/LemLib.lean lean-lib/LemLib/*.lean lean-lib/LemLibTheorems.lean
lean-lib/LemLibPmapLaws.lean lean-lib/LemLibTest.lean` → every count 0.

`tests/nonlean-regress/run.sh`:
`nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)`
— no rebaseline (the tails rule touches no non-Lean emitter; invariance
witness above).

Cerberus OCaml tree, this lem vs `ecf75b4` (§2.7): `OCAML DIFF exit 0 lines 0` (86/86 files).


## 8. Audit response (pre-merge audit `2026-09-05_tails-pmap-audit-premerge.md` @ `f6e10d2`: MERGEABLE, no MAJOR; F1–F3 MINOR, 7 NOTEs)

One commit (this commit, the audit-response commit — the fourth of the branch). Every quoted output verbatim from this
worktree after the fix (`.tmp/suite-2.log`, `.tmp/nonlean-2.log`,
`.tmp/leanlib-3.log`).

- **F1 (capture through a Lean `target_rep` spelled like a synthesized
  binder).** The hoist's constant check compared `lemTail` with referenced
  constants' LEM names only; a constant with ``target_rep function dl =
  `lemTail` `` rendered as the binder (audit probe `p11b`: Lean 4 vs OCaml
  1), and the same hole existed at `ecf75b4` for `lemFuel` (`p11c`), the
  reserved-binder scan looking at binders only. Fix, one generic check
  (`lean_reserved_capture_check`, `src/lean_backend.ml`; mechanism comment
  there): for every constant a clause body references, the identifiers its
  Lean rep renders as (`CR_simple`/`CR_inline` bodies — every `Backend`
  ident —, `CR_infix`, `CR_special_rep` text) and its lem name, plus every
  `Backend` ident written directly in the body, are compared against the
  reserved set — exact `lemFuel`, `lemMeasureLe`, `LemFuel`, `lemTail`,
  prefixes `_lemReader_`/`_lemSupply` — and any hit is refused naming the
  constant and the text. Run in `reserved_binder_check` (every fuel'd /
  reader / supply group) and in `lean_hoist_tail_binders` (every hoist,
  so `structural`-only hoists are covered too). Negatives
  `neg_tail_rep_capture.lem` (`p11b`) and `neg_fuel_rep_capture.lem`
  (`p11c`); the refusals, verbatim:

  ```
  Error: Lean backend: the body of bad references constant dl, which renders on Lean as `lemTail` — a reserved synthesized binder name (the reserved-name contract: 'lemFuel', 'lemMeasureLe', 'LemFuel', 'lemTail' and the '_lemReader_'/'_lemSupply' prefixes are the backend's); inside the generated worker that identifier is CAPTURED by the synthesized binder and computes a different value than the OCaml target (pre-merge audit 2026-09-05, probe p11b) — rename the constant or its Lean target_rep
  Error: Lean backend: the body of g references constant seven, which renders on Lean as `lemFuel` — a reserved synthesized binder name (the reserved-name contract: 'lemFuel', 'lemMeasureLe', 'LemFuel', 'lemTail' and the '_lemReader_'/'_lemSupply' prefixes are the backend's); inside the generated worker that identifier is CAPTURED by the synthesized binder and computes a different value than the OCaml target (pre-merge audit 2026-09-05, probe p11b) — rename the constant or its Lean target_rep
  ```

  Consequence for §7 decision 4: `lemTail` now IS in the generic reserved
  set for every fuel'd/reader/supply definition's referenced constants
  (the binder scan itself is unchanged); the constant-name side of the
  contract is uniform across all reserved names. The lem-name check is
  kept alongside (a constant without a rep renders as its lem name).
  Stricter than `ecf75b4` only for programs that were silently wrong.
- **F2 (generic `CmpLaws` bridge).** `theorem Pmap.cmpLaws_of_transOrd
  {α : Type} [Ord α] [Std.TransOrd α] : Pmap.CmpLaws (defaultCompare : α →
  α → LemOrdering)`. Hypothesis choice: `defaultCompare` is `compare`
  read into `LemOrdering` (`LemLib.lean:138`), and Lean core's
  `Std.TransOrd α` (= `Std.TransCmp (compare : α → α → Ordering)`,
  `Init/Data/Order/Ord.lean`, present in both 4.28.0 and 4.32.2 with the
  same names) packages exactly the four laws: `OrientedCmp.eq_swap`
  (`flip`; reflexivity via the `OrientedCmp → ReflCmp` instance),
  `TransCmp.lt_trans`, `TransCmp.congr_left` (`eq_congr`). No
  LemLib-local class was needed. Instances in core cover `Nat`, `Int`,
  `String`, `Char`, `Bool`, fixed-width ints, `Fin`, `Option`, and
  lexicographic products. Pins: `cmpLaws_defaultCompare_nat'`, `_int`,
  `_string` by the bridge; `decide`/`rfl` on closed `Int`- and
  `String`-keyed maps; the laws instantiated at `Int`/`String` through
  the bridge. Verbatim:

  ```
  info: LemLibPmapLaws.lean:555:0: 'Pmap.cmpLaws_of_transOrd' depends on axioms: [propext]
  info: LemLibPmapLaws.lean:556:0: 'Pmap.cmpLaws_defaultCompare_int' depends on axioms: [propext, Classical.choice, Quot.sound]
  info: LemLibPmapLaws.lean:557:0: 'Pmap.cmpLaws_defaultCompare_string' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

  (the classical axioms at `Int`/`String` come from core's `TransOrd`
  instances, not from this file.) The consumer's `Ord sym` (cerberus
  `symbol.lem:169`: digest compare, then `nat`) is `defaultCompare` of a
  hand-written `Ord` instance: provable through the bridge once that `Ord`
  carries `Std.TransOrd sym` (a lexicographic pair of `String`/`Nat`
  compares, both `TransOrd`; an `⟨eq_swap, isLE_trans⟩` instance over
  `compareLex`, or by hand), else by proving `CmpLaws` directly as the
  `Nat` witness does — the consumer's call.
- **F3 (doc precision: any trailing lambda is hoisted).** Documented as
  the general rule (§2.2, §2.3; manual; DESIGN table row and paragraph)
  rather than gated on the `remove_function` tag: extensionally equal,
  zero cerberus impact (the tree without the new declares is byte-identical
  under both lems — the auditor's measurement), simpler to state, and a
  measure over the user binder needs exactly this. `p13` is now the
  positive `tuser` in `test_function_tails.lem` (h) with its obligation
  proof and kernel pins; before (fuel only) / after (fuel + measure),
  verbatim (`.tmp/tuser-before-after.diff`):

  ```
  28,30c28,30
  <  def  tuser_lemFuel (lemFuel : Nat)  (n : Nat)  : Nat → Nat := match lemFuel with
  <   | 0 => (fun _ => 0)
  <   | Nat.succ lemFuel => ( fun (k : Nat) =>  if  n  ==   0 then  k  else (tuser_lemFuel lemFuel)  (n  -   1)  (k  +   1))
  ---
  >  def  tuser_lemFuel (lemFuel : Nat)  (n : Nat) (k : Nat)  : Nat := match lemFuel with
  >   | 0 => ((fun _ => 0) k)
  >   | Nat.succ lemFuel => ( if  n  ==   0 then  k  else (tuser_lemFuel lemFuel)  (n  -   1)  (k  +   1))
  32,34c32,34
  < def tuser [LemFuel] : Nat → Nat → Nat := tuser_lemFuel LemFuel.fuel
  < theorem tuser_lemFuel_zero ( n : Nat) :
  <     (tuser_lemFuel 0  n : Nat → Nat) = (fun _ => 0) := rfl
  ---
  > def tuser ( n : Nat) ( k : Nat) : Nat := tuser_lemFuel (n + 1)  n  k
  > theorem tuser_lemFuel_zero ( n : Nat) ( k : Nat) :
  >     tuser_lemFuel 0  n  k = ((fun _ => 0) k) := rfl
  ```
- **N7.** `[AGENT]` tags on each §7 decision item.
- N1–N6 need no change (N4: the `body_free` clause is unreachable in
  practice and kept as belt-and-braces; N5/N6 are the record's own
  caveats).

Gates re-run after the response, verbatim:

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
  OK (rejected as declared): negative/neg_fuel_rep_capture.lem
  OK (rejected as declared): negative/neg_tail_body_binder.lem
  OK (rejected as declared): negative/neg_tail_rep_capture.lem
  OK (rejected as declared): negative/neg_tail_shadow_param.lem
  OK (rejected as declared): negative/neg_tail_user_shadow.lem
  OK: inv_function_tails.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: parity (11 lines byte-identical to the OCaml reference; pin matches)
  OK: 8 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
  OK: 248 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make lean  380.20s user 23.06s system 93% cpu 7:11.55 total
exit 0
```

(all 81 negative probes and 7 invariance witnesses OK; the parity phase's
four `FAIL` lines are the same four registered XFAILs — `f_int32_overflow`,
`f_int_of_big_num`, `p_str_bytes`, `p_str_escapes`.) The `tuser` obligation:
`'Test_function_tails_lemMeasureProofs.tuser_measure_sufficient' depends on axioms: [propext, Quot.sound]`.

`lean-lib` `lake build`: `Build completed successfully (39 jobs).` — the
nine `#print axioms` lines (the six of §3.1 unchanged, the three of F2
above). `grep -c "^axiom "` over `lean-lib/*.lean`, `lean-lib/LemLib/*.lean`
→ every count 0.

`tests/nonlean-regress/run.sh`:
`nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)`.

The cerberus OCaml byte-identity of §2.7 is unaffected by the response
(the changes are two refusals and a rule for Lean emission only; the
invariance witness and the net above are the evidence).

## 5. TODO rows

- 17 — RESOLVED (this record); row kept with its original text.
- 19 (new) — the `Pmap` laws request, DELIVERED; the unrequested
  `Pset`/`remove`/`bindings` follow-ups listed on the row.

## 6. Doc changes

`doc/lean-backend/README.md` (the manual's fuel/measure paragraph: the
tail rule and `lemTail`), `DESIGN.md` (the declare table's "point-free
`function` tails" row; the measure paragraph), `TODO.md` (rows 17, 19),
`lean-lib/README.md` (the theorem files), `lean-lib/lakefile.lean`
(`LemLibPmapLaws` default target).

## 7. Decisions for the operator

1. [AGENT] **The comparator hypothesis is a strict WEAK order** (`Pmap.CmpLaws`:
   `refl`/`flip`/`lt_trans`/`eq_congr`), weaker than the consumer's
   "strict total order" and the honest one for a comparator-keyed map
   whose `add` replaces on EQ. If the consumer prefers the `EQ ↔ =`
   formulation, it is an instance (prove `CmpLaws` for their comparator
   as `cmpLaws_defaultCompare_nat` does); the laws themselves stay
   comparator-relative. Nothing to change unless they want a derived
   `find?_add_other'` with `k ≠ k'` under an `EQ ↔ =` hypothesis — S.
2. [AGENT] **`Fmap.WF cmp` pins the CAPTURED comparator to `cmp`** (a function
   equality). The generated environments insert with one static
   comparator, so this is the natural invariant; a consumer that
   threads maps built under a different-but-equal comparator would need
   extensional equality of the two — the alternative (WF quantifying over
   the captured comparator) makes the `_other` law's hypothesis
   `c k k' ≠ EQ` about the captured `c`, which the caller cannot see.
   Kept the pinned form.
3. [AGENT] **Dry-run measures for the two shared-counter mutual blocks are
   acceptance witnesses, not sufficiency claims.** `get_ctx`/`get_ctx_unseq_aux`
   share one counter: `lemSize g + 1` bounds the call DEPTH through the
   expression only if every hop descends (it does — each `get_ctx` call is
   on a subexpression and each `get_ctx_unseq_aux` step on a shorter list,
   but the list's own steps do not decrease `lemSize g`… of the ELEMENT: the
   right joint measure is one per member such that every cross-call
   strictly decreases the CALLEE's measure — the cerberus half's proof
   will fix the exact expressions; `List.length lemTail + 1` for the aux
   is too small when an element's `get_ctx` recursion is deep). Likewise
   the ail trio: `are_compatible_params_aux` recurses into `are_compatible`
   on ctypes, so `List.length lemTail.1 + 1` alone cannot be sufficient —
   a size over the list's ctypes is needed (the derived container helper
   `ctype_.lemSize_aux1` exists for `Function`'s parameter list; a
   measure may name it as a qualified global). What this slice
   establishes: the mechanism accepts and generates all six; the
   measures' proofs are C1's remaining work, as for every measured row.
4. [AGENT] **`lemTail` and the reserved-name contract.** The name is checked
   locally (refused wherever a hoist would collide) but NOT added to the
   global reserved scan (`lemFuel`, `lemMeasureLe`, `_lemReader_*`,
   `_lemSupply*`), so a definition without a tail may still bind
   `lemTail`. Making it globally reserved is a one-line change; kept
   local so as not to refuse code the rule never touches. Operator's
   call; either way the manual states the name.
5. [AGENT] **Sentinel typing under the hoist.** The fuel payload stays written at
   the head's original (function) codomain and is APPLIED to the hoisted
   binders — the cerberus declares (`fuelExhausted (fun _ => none)`,
   `fuelExhausted (fun _ => acc)`) need no edit. A payload written for
   the post-hoist shape would fail to typecheck (loud). Documented in the
   manual; no alternative was built.


## 9. Orchestrator boundary review [AGENT, orchestrator, 2026-09-05]

Independent re-verification, lem rebuilt from source in this worktree, at
`a30b0bc` (the slice) and at `0875d6a` (audit response `b034e7c` + the
audit document `f6e10d2` cherry-picked). Final run, verbatim:

```
Lem 0875d6a
Build completed successfully (39 jobs).          (lean-lib)
0                                                (grep "^axiom " lean-lib → none)
=== Generation: 53 passed, 0 failed, 0 skipped ===
Build completed successfully (160 jobs).
  OK: 248 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make-lean-rc=0
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
```

(the four `FAIL` lines in the run are the registered XFAILs.) Pre-merge
audit `2026-09-05_tails-pmap-audit-premerge.md` (MERGEABLE, no MAJOR; the
F1 capture hole — a pre-existing class for `lemFuel` too — closed generically
in `b034e7c`, with F2's `Std.TransOrd` bridge and F3's rule statement). The
cerberus OCaml byte-identity (86/86, diff 0) and the Lean-tree identity
without new declares (170/170) were verified by the auditor in a fresh
checkout; not re-run here. Merge ask goes to the operator on this head.
