# Structural-declare slice — record (2026-09-04)

Branch `arc/structural-declare` (lem-lean), base mainline `mdd/lean-backend`
@ `9ba8970` (the merged fuel-parameter arc). Charter: the orchestrator's
response to the consumer's review, cerberus-lean
`lean_frontend/docs/2026-09-04_fuel-parameter-consumer-review-response.md`
§3–§4 (the structural declare as the mechanism for the consumer's form
(A); D4 as ruled; monotonicity, TODO row 13). Worker [AGENT] (lem-lean);
rulings paraphrased with [USER] provenance; every quoted output is
verbatim from this worktree; tallies marked "derived" are derived.
Nothing merged, nothing pushed.

## 0. Commits

| Commit | Content |
|---|---|
| `d8bbb4e` | Backend: `declare {lean} structural val` (lexer/parser/ast/typed_ast/typecheck/echo/Ott; `lean_structural_check`, `lean_structural_assign`, emission with `termination_by structural`); tests (positive module + kernel pins, 11 negative probes, parity probe + pin, invariance witness, contextual keywords); manual, DESIGN, README |
| `3c1846b` | D4 = WRAP: LemLib + `num.lem` reps, `Exact` conversions deleted, `f_int32_overflow` registered, rulings addendum, DESIGN, nonlean goldens rebaselined (27 human/echo rows) |
| `76b76da` | Fuel monotonicity: hand-proved Route-B exemplar `TestFuelMonoExemplar.lean` (+ lakefile root) |
| (this record's commit) | record, TODO rows 10/11/13, design note R2 |

## 1. The rulings this slice implements

- [USER 2026-09-03] general form: any value that a context or theorem can
  quantify over is fine; any hardcoded magic value that cannot be
  quantified over is by definition a bug, unless it mirrors a lem or
  ISO-C design choice; OCaml limits hardcoded because of OCaml-level
  execution issues are forbidden as well — the logical semantics is what
  counts.
- [USER 2026-09-04], adopting the orchestrator's recommendations (proceed
  with the merges as proposed, then work on this as suggested) —
  D4 = WRAP; the structural declare is the mechanism for the consumer's
  form (A).
- The consumer's requirement (refined-cerberus review §2, [AGENT],
  accepted into the charter): every fuel'd function reachable from
  `drive` is (A) structural on its data, (B) absorbing typed exhaustion,
  or (C) unreachable; and its D2 recommendation (i): make the three
  equalities structurally recursive in the model.

## 2. The structural declare — design decisions, with reasons

**Name and form.** `declare {lean} structural val f` — a per-target
declare in the family's style (`fuel val`, `supply val`, `reader val`),
`structural` a contextual keyword like the others (usable as an
identifier everywhere else: `test_contextual_keywords.lem`). "Structural"
names the classic PL mechanism exactly (structural recursion, checked by
Lean's `brecOn` translation); `total`/`terminating` would have promised
less than what is delivered (a well-founded definition is total too).

**Contract.** A recursive definition so declared is emitted as an
ORDINARY Lean `def` — no `partial`, no `_lemFuel` worker, no `[LemFuel]`
of its own — followed by `termination_by structural <param>`. Lean must
prove termination by structural recursion on the designated parameter.

**The well-founded fallback is FORBIDDEN [AGENT], reason.** Without a
clause Lean tries structural recursion and silently falls back to
well-founded recursion. Both give a `def`, but a well-founded definition
is `@[irreducible]`: closed-term `decide`/`rfl` stop at it — precisely
the consumer's `join` finding that motivated form (c). A declare whose
promise is "the kernel computes through f" cannot let the checker trade
that away for a keyword. So the clause names the parameter and the
fallback is off. The cost is that the backend must DESIGNATE the
parameter (Lean's syntax `termination_by structural x` requires a
parameter name — measured in the probe, §3: a pattern variable is
"Unknown identifier"), hence the analysis below. `declare {lean}
termination_argument f = automatic` (lem's upstream vocabulary) is kept
with its existing meaning — a plain `def`, NO clause, fallback allowed —
and documented as such; the two on one val are refused (ST-term) as
contradictory.

**The structural-parameter analysis (`lean_structural_assign`,
`src/lean_backend.ml`).** Mirrors what Lean's checker will accept, on the
typed AST after lem's own pattern compilation: a variable's LEVEL relative
to the definition's parameters is exact (the parameter itself, or a `let`
alias of it) or strict (bound by a constructor pattern — variant
constructor, `::`, list literal, record pattern, `n+k`, or a tuple INSIDE
one of those — in a match whose scrutinee is at level exact/strict of
that parameter; a match on a tuple OF variables binds component-wise, as
the renderer's multi-discriminant match does; a tuple pattern at the top
of a match on one variable does not descend; shadowing removes a name).
Every application whose head is a member of the block is a call; a member
in any other position (passed to `List.map`/`List.all`, partially applied
under a lambda) is refused outright. The designated position of each
member: at every call from f to g, g's designated argument is at level
strict(f's position); an exhaustive search over the named parameters,
first assignment in parameter order (Lean infers in the same order); a
truly mutual block is assigned together (every member carries the
declare, all-or-none, as for fuel — Lean wants a clause on each). Where
no assignment exists the refusal names, per named parameter, the first
breaking call and why (not a variable / a variable not bound by a
constructor pattern on that parameter / the parameter itself).

**What is NOT structural on this backend, and why (each a negative
probe):**
- a self-reference as a VALUE (`List.map f`, `List.all (uncurry f) (zip
  …)`, `listEqualBy f`): Lean's checker cannot eliminate such a
  recursive application (`failed to eliminate recursive application`);
  the rewrite is an explicit list-walking sibling — `neg_structural_hof`;
- a computed argument (`f (n - 1)`) — `neg_structural_nosubterm`;
- a nat recursion through an `m + 1` pattern: the Lean target desugars
  n+k patterns to guards (`if n = 0 … else let m0 = n - 1 …`, the
  pre-existing fix #11), so the argument is a let-bound arithmetic value
  — `neg_structural_natpat`;
- a record pattern on a recursive record type: lem compiles it to a match
  on the field projections, and Lean's checker cannot see through a
  projection — `neg_structural_record` (the Lean error is quoted in §3);
- a lambda parameter shadowing the subterm's name — `neg_structural_shadow`.

**Refusal classes at generation (fail-closed, each a probe):** ST-fuel
(`fuel` + `structural` on one val), ST-term (`termination_argument` +
`structural`), ST-inert (`structural` on a val with a Lean target_rep —
the FC-inert rule), ST-nonrec (`structural` on a non-recursive
definition: [AGENT] REFUSED rather than accepted-as-no-op, because an
inert declare is a lie in the source — the same reasoning that refuses a
fuel sentinel on a rep'd val), multi-clause definitions (the equation
form has no parameter name to designate; write one match), part of a
mutual block (all-or-none).

**Where the check lives.** Generation refuses everything the analysis
can see. Where the analysis designates a parameter and Lean's checker
still disagrees, the Lean BUILD fails loudly — the fail-closed backstop,
exactly as for `fuel_consumer` (N1): generation succeeds, the build
refuses, nothing is absorbed. During development this backstop fired
once (a permissive field-projection rule), the rule was tightened to
match the checker, and the case became `neg_structural_record`; no lem
construct is known that passes the analysis and fails the checker (the
cerberus census below is the largest test of that claim — §6 reports
every Lean-side verdict).

**Interaction with the other liftings.** A structural def that calls a
fuel'd def is fuel-lifted like any def (it takes `[LemFuel]`; its own
recursion needs no counter — `spin_each` in `test_structural.lem`,
pinned at two fuels). Reader/supply lifting compose unchanged (the
designated argument is still the variable). Because a structural def is
an ordinary def, it CAN be an instance method's implementation — the
fuel scope rule does not apply — which is how D2 resolves (§6).

**Plumbing** mirrors `fuel_consumer` exactly: lexer (contextual keyword
`structural`), parser (`Declare targets_opt Structural Val id`), `ast.ml`
`Decl_structural_decl`, `typed_ast.ml(i)` `Decl_structural` and the
`const_descr` field `structural : Targetset.t`, `typecheck.ml`,
`convert_relations.ml`, the human-target echo in `backend.ml`, the Ott
row `structural_decl`. The OCaml/HOL/Isabelle/Coq emitters never see the
declare (`emp`), so their output is untouched by construction (§7 measures
it). ocamlyacc at the final grammar, verbatim: `5 rules never reduced` / `2 shift/reduce conflicts, 2 reduce/reduce conflicts.` — unchanged from the fuel-parameter arc's baseline.

## 3. Before / after — one function, verbatim

`tests/comprehensive/test_structural.lem`, `len` and the mutual pair
`tsum`/`tsums` (a variant with a nested `list tree`). BEFORE (the
`9ba8970` lem on the same source with the declares stripped — the
baseline cannot parse the declare):

```lean
 partial def  len  (l : List (Nat))  : Nat := 
  match  l with  |  [] =>   0 |  _  ::  xs =>   1  +  len  xs
  
…
 partial def  tsum  (t : tree)  : Nat := 
  match  t with  |  Leaf  n =>  n |  Node  ts =>  tsums  ts
  
partial def  tsums  (ts : List (tree))  : Nat := 
  match  ts with  |  [] =>   0 |  t  ::  ts' =>  tsum  t  +  tsums  ts'
  
end
```

AFTER (this lem, `Test_structural.lean`):

```lean
 def  len  (l : List (Nat))  : Nat := 
  match  l with  |  [] =>   0 |  _  ::  xs =>   1  +  len  xs
  
termination_by structural l
…
mutual
 def  tsum  (t : tree)  : Nat := 
  match  t with  |  Leaf  n =>  n |  Node  ts =>  tsums  ts
  
termination_by structural t

def  tsums  (ts : List (tree))  : Nat := 
  match  ts with  |  [] =>   0 |  t  ::  ts' =>  tsum  t  +  tsums  ts'
  
termination_by structural ts

end
```

Kernel computation through them (`lean-test/TestStructuralCheck.lean`,
checked at build time): `example : len [1, 2, 3] = 3 := by decide`,
`… := rfl`, `example : tsum (Node [Leaf 1, Node [Leaf 2, Leaf 3], Leaf 4])
= 10 := by decide`, inductive proofs over the equation lemmas
(`len_append`, `rev_acc_length`); verbatim:
`'TestStructuralCheck.len_append' depends on axioms: [propext, Quot.sound]`,
`'TestStructuralCheck.rev_acc_length' depends on axioms: [propext, Quot.sound]`.

The Lean-side backstop, verbatim (Lean 4.28.0, the development run on
`chain_len` before the analysis was tightened — the record pattern
compiled to `match c.head, c.tail with | _, some c' => 1 + chain_len c'`):

```
✖ [33/35] Building Test_structural (279ms)
error: Test_structural.lean:128:1: failed to infer structural recursion:
Cannot use parameter c:
  failed to eliminate recursive application
    chain_len c'
error: Lean exited with code 1
```

and the probe that fixed the syntax (Lean 4.32.2, `.tmp/probe-struct`,
`termination_by structural n` on `bad (n - 1)` and `termination_by
structural xs` naming a pattern variable):

```
error: A.lean:1:0: failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    bad (n - 1)
error: A.lean:7:26: Unknown identifier `xs`
```

Lake did NOT build the downstream module `B` after `A` failed — which is
why the cerberus census (§6) runs in rounds.

## 4. D4 — WRAP (the `int32`/`int64` conversions)

[USER 2026-09-04] adopting the fuel-parameter record's D4 recommendation
(proceed with the merges as proposed, then work on this as
suggested). lem's own semantics of `int32FromInteger`/`int32FromNatural`/
`int32FromNumeral` and the `int64` trio is modular — the prover-side reps
are `word_of_int` (Isabelle) / `n2w` (HOL), `library/num.lem:831-832`,
`:1040-1041`, `:2378-2470`; `Nat_big_num.to_int32/to_int64: Overflow` is
the OCaml backend's raise, an OCaml-execution artifact of the X3 kind.
Change: `library/num.lem` Lean reps `int32FromNatural = lemInt32OfNat`,
`int32FromInteger = lemInt32OfInt`, `int64FromNatural = lemInt64OfNat`,
`int64FromInteger = lemInt64OfInt` (the modular conversions that already
served `int32FromNat`/`int32FromInt`); `lemInt32FromNumeral`/
`lemInt64FromNumeral` are `Int32.ofNat`/`Int64.ofNat`;
`lemInt32OfIntegerExact`, `lemInt32OfNaturalExact`,
`lemInt64OfIntegerExact`, `lemInt64OfNaturalExact` DELETED (measured: no
other user in `lean-lib/`, `library/`, hand-written tests — the only
generated uses were through the four reps). The LemLib comment block at
the fixed-width section states the rule; `DESIGN.md`'s numbers paragraph
and the deviation list are updated; `2026-09-03_exception-case-rulings.md`
carries the D4 addendum (closes TODO row 11).

Parity evidence (this tree, `tests/comprehensive/parity/run.sh`):
```
=== f_int32_overflow ===
  ocaml: failed as expected (exit 2): Fatal error: exception Failure("int32_of_big_int") 
  FAIL: failure probe, but the Lean binary SUCCEEDED (exit 0) where the OCaml reference fails
  XFAIL (expected, registered): RULED OCaml-target deviation ([USER 2026-09-04] adopting the fuel-parameter record's D4 recommendation — …
=== p_int_wrap ===
  OK: parity (42 lines byte-identical to the OCaml reference; pin matches)
```

(`p_int_wrap`'s 42 rows include the in-range `int32FromInteger 2147483647`
/ `int64FromInteger …` conversions and every `Int32.of_int`/`of_nat`
wrap — unchanged.) The suite's XFAIL count is 4 (was 3): the two F2
strings rows, `f_int_of_big_num` (X3), `f_int32_overflow` (D4).

## 5. Monotonicity (TODO row 13) — assessed, exemplar landed, generation not built

The brief: implement the auditor's Route B (`f_completes` + `f_mono`) if
S–M; if L, land the declaration + predicate generation, leave theorem
generation specified with a hand-proved exemplar. Assessment [AGENT]:
**L on both routes, and the declaration alone would be vocabulary without
mechanism — not added.** Reasons, measured against the backend:

- *Route B (audit N6).* The completion predicate must mirror the worker's
  CONTROL skeleton with every recursive call replaced by `f_completes n e`
  and the body's VALUES dropped; where a body's control depends on a
  sub-result (`if f (n-1) x = 999 then …`), the predicate must carry the
  sub-result too — a Bool-writer instrumentation of the whole body. That
  is the supply transform's shape (`supply_thread`, ~400 lines, with its
  G-λ/G-bare/G-arity refusals): a recursive call inside a lambda passed to
  `List.map`/`foldl` cannot be threaded, and cerberus's evaluators are
  written that way. Then the theorem `f_completes n x → f_lemFuel (n+1) x
  = f_lemFuel n x` needs a GENERATED tactic script following the body's
  case structure (one `split`/`ih` per branch and call), and the erasure
  lemma relating the instrumented copy to the worker. Per-body proof
  generation is the L part; the predicate is not separable from it.
- *Route A (record §5, the consumer's phrasing).* A declared monad with an
  absorbing outcome makes monotonicity a theorem only if every body is
  STRICT in its sub-results (consumes them through `bind` alone). That is
  a property of each body, not checkable syntactically in general, and
  for cerberus's ND monad the kill is a VALUE inside a state function
  (`ND (fun st => (NDkilled …, st))`) — "≠ ⊥" is not statable at the
  monad level and `nd_bind` is itself fuel'd. The vocabulary (which
  monad, which element, which law) is non-Lean-visible grammar and an
  operator decision — recorded under §9.

What landed: `tests/comprehensive/lean-test/TestFuelMonoExemplar.lean`, the
exact statement shape a generator would have to produce, proved by hand
over the GENERATED worker `spin_lemFuel` of `test_fuel_param.lem`:
`spin_completes : Nat → Nat → Bool` (0 ↦ false; n+1 ↦ the body's control
with the call replaced), `spin_completes_mono`, `spin_mono : spin_completes
n x = true → spin_lemFuel (n+1) x = spin_lemFuel n x` (induction on the
counter generalizing x; one `split`, one `ih` — the generated proof's
template), the corollaries `spin_completes_le`, `spin_stable` (completes
at n ⇒ the same value at every m ≥ n; function-independent given the two
lemmas) and `spin_fuel_irrelevant` at the WRAPPER (`@spin ⟨f⟩ x = @spin
⟨g⟩ x` for two completing fuels), plus `decide` witnesses that the
predicate computes. Kernel-only tactics, no option bump; verbatim:
```
ℹ [139/140] Built TestFuelMonoExemplar (212ms)
info: TestFuelMonoExemplar.lean:90:0: 'TestFuelMonoExemplar.spin_stable' depends on axioms: [propext]
info: TestFuelMonoExemplar.lean:91:0: 'TestFuelMonoExemplar.spin_fuel_irrelevant' depends on axioms: [propext]
```

The precise generator specification (TODO row 13, updated) is the
exemplar's four declarations with `spin` abstracted: for a fuel'd `f`
with parameters `xs`, worker body `B[f_lemFuel lemFuel]`, emit
`f_completes : Nat → xs → Bool` := `| 0, _ => false | n+1, xs => B^c` where
`B^c` is `B` with every `f_lemFuel n e` ↦ `f_completes n e`, every
non-Bool value-producing subterm not on a control path dropped, `&&` at
sequenced calls; `theorem f_completes_mono` and `theorem f_mono` by
`induction n generalizing xs` with the body's `split`s and one `exact ih
_ h` per call; `f_stable`/`f_fuel_irrelevant` are generic over those two.

## 6. The (A) census for the cerberus half (read-only dry run)

Method (read-only; nothing in cerberus-lean touched): `frontend/` of
cerberus-lean primary @ `1b57bcf26` copied to `.tmp/cerb/`; the five
numeric fuel declares deleted (this lem refuses them — the fuel arc's
rule); `LEM_SRC_LEAN` (85 files) and the Makefile's flags obtained with
`make -C cerberus-lean --eval`; `LEMLIB` = this tree's library. Driver:
`.tmp/cerb/census_gen.py` — EVERY one of the 67 sentinel fuel declares
turned into `declare {lean} structural val`, lem run, the first refusal
recorded with its message and that function's declare REMOVED (a plain
`partial def`, so the run can continue; a refused member of a truly
mutual `let rec … and` block takes its siblings — the all-or-none rule),
repeat until lem exits 0: 60 rounds of ~18 s. Every refusal is the
backend's generation-time analysis; none reached Lean's checker, so the
Lean 4.32.2 build phase (`census_lean.py`, written and ready) had
nothing to adjudicate.

**Result: 0 of 67 are structural AS WRITTEN.** Every function was
refused at generation, each with the parameter, call and reason. Classes
(derived from the messages): UNTRACKED 35 (the designated argument at some
self-call is a variable bound by a lambda/let or by a match on a computed
scrutinee — e.g. `memValueFromValue` matches `unatomic ty1`, so its
subterms are not the parameter's; `ctypeEqual`'s call sits in the local
`paramsEqual` lambda fed to `List.all … (zip …)`), COMPUTED 9 (the
argument is arithmetic or an application — the counter-style helpers
`mkListN_aux`, `mkListFromTo_aux`, `replicate_list_`, the bit-twiddling
`tmp_*_aux`, the driver loop's accumulator), HOF 10 (the function itself
passed as a value: `eq_core_base_type` via `listEqualBy`,
`fake_mem_value_eq`/`has_concurRead`/`has_ccall` via `List.all`/`zip`,
`convert_pexpr`/`convert_expr`/`collect_saves_aux`/`driver2` via
`List.map`/folds), SAME 2 (`in_pattern`, `easy_update_mem_value_aux`: the
argument is the parameter itself — recursion on a different, computed
argument), CROSS-CALL 3 (`get_ctx`/`get_ctx_unseq_aux`, `many`/`many1`,
`liftND`/`liftAction`: no assignment of structural positions makes the
mutual block's cross-calls structural), SIBLING 8 (removed with a refused
mutual sibling).

Spot-checked verdicts (the analysis is faithful, not over-strict): a
minimal probe of the destructuring-parameter shape (`let rec cteq (Ct _
ty1) (Ct _ ty2) = match (ty1, ty2) with (Arr t1 _, Arr t2 _) -> cteq t1
t2 …`) IS accepted (`.tmp/probe2/probe_destr.lem`); `ctypeEqual` is
refused for its `paramsEqual` lambda, not its parameters;
`memValueFromValue` for `match unatomic ty1 with` (Lean's checker would
say the same: `ty_` is a subterm of `unatomic ty1`, not of `ty1`);
`nd_bind` for `List.map (fun (str, m) -> … nd_bind m f) str_ms`;
`mkUnspec` for `List.map (fun (ident, (_,_,_,ty)) -> … mkUnspec ty)` over
`Ctype_aux.get_structDef tag_sym` (the recursion is on the tag
environment, not on the argument); `to_pure` for `to_pure e` where `e`
comes from `subst_pattern pat pe1 e2`.

**What this means for the cerberus half (the (A)/(B)/(C) classification).**
Nothing in the 67 is (A) by declaration alone; (A) is available where the
recursion IS on the data and only the SHAPE blocks the checker — the
higher-order traversals (HOF and the lambda-bound UNTRACKED rows) become
explicit list-walking siblings in the same mutual block (the D2
demonstration below is exactly that rewrite, three functions, a handful
of lines each); where the recursion is on a computed value (`unatomic
ty1`, a tag lookup, an accumulator or a counter) the function is not
structural on its argument and stays (B) — a fuel'd (B)-shaped recursion
with an absorbing payload, or a data-measure index in a hand-written rep
(form (c) of the other kind); the driver/ND family is genuinely partial
and is (B) as the consumer already said. The per-function table is the
census the half asked for; the "first error line" is the backend's own
message, which names the site to rewrite.

**The D2 demonstration (the three equalities, option (i)).** In the COPY
only: `ctypeEqual`'s `List.all (uncurry paramsEqual) (List.zip params1
params2)` → a sibling `ctypeParamsEqual` walking both lists;
`eq_core_base_type`'s `listEqualBy eq_core_base_type` → `eq_core_base_types`;
`fake_mem_value_eq`'s `List.all (uncurry fake_mem_value_eq) (zip …)` →
`fake_mem_values_eq`. Semantics mirrored exactly, and a finding for the
cerberus half: `zip` TRUNCATES, so the two `List.all … (zip …)`
equalities compare the COMMON PREFIX only and return `true` on a length
mismatch (the rewrite keeps `| _ -> true`; `listEqualBy` returns `false`
and its rewrite keeps that). Both members of each pair carry the
structural declare (all-or-none). Generation: `lem exit 0` — the analysis
designates `c`/`ps1`, `bTy1`/`l1`, `mval1`/`l1`; the three `instance (Eq
…)` methods render (`isEqual := ctypeEqual`, `isEqual :=
eq_core_base_type`, `isEqual := fake_mem_value_eq`) with NO fuel-scope
error — D2 resolved as the consumer recommended. Generated heads, verbatim:

```
 def  ctypeEqual  (c : ctype) (c0 : ctype)  : Bool := match c, c0 with | ( Ctype  _  ty1), ( Ctype  _  ty2) => ( let  ord  := fun (x : …
def  ctypeParamsEqual  (ps1 : List ((qualifiers ×ctype ×Bool))) (ps2 : List ((qualifiers ×ctype ×Bool)))  : Bool := match ps1, ps2 …
    isEqual    :=  ctypeEqual
 def  eq_core_base_type  (bTy1 : core_base_type) (bTy2 : core_base_type)  : Bool := 
termination_by structural bTy1
def  eq_core_base_types  (l1 : List (core_base_type)) (l2 : List (core_base_type))  : Bool := 
termination_by structural l1
    isEqual   :=  eq_core_base_type
 def  fake_mem_value_eq  (mval1 : impl_mem_value) (mval2 : impl_mem_value)  : Bool := 
termination_by structural mval1
def  fake_mem_values_eq  (l1 : List (impl_mem_value)) (l2 : List (impl_mem_value))  : Bool := 
termination_by structural l1
    isEqual   :=  fake_mem_value_eq
```

Lean 4.32.2 build of exactly those three modules (`lake build +Ctype
+Core +Defacto_memory_aux` in a copy of cerberus's `lean_frontend` with
its `.lake` cache and the pinned LemLib `3c88f0d` — sufficient because
the tree then carries no `LemFuel`; the three regenerated modules and
their auxiliaries installed over `generated/`, everything else as in the
tree): verbatim
(`.tmp/cerb/d2-build.log`; warnings are the pre-existing derived-comparison
`unused termination_by` notes in other modules):

```
⚠ [54/76] Built Ctype (643ms)
⚠ [74/76] Built Defacto_memory_aux (503ms)
⚠ [76/76] Built Core (2.8s)
Build completed successfully (76 jobs).
CERB_MEM_MAX=16G  lake build +Ctype +Core +Defacto_memory_aux  126.74s user 3.84s system 122% cpu 1:46.17 total
EXIT 0
```

Zero `error:` lines: Lean 4.32.2's structural checker accepted all six
definitions — mutual structural recursion over the nested inductives
(`ctype`/`ctype_` through `List (qualifiers × ctype × Bool)`,
`core_base_type` through `List core_base_type`, `impl_mem_value` through
`List impl_mem_value`) — and the `Eq0` instances built on them. This is
the (A) shape the cerberus half applies at those three sites.

`monStep` (`cmm_op.lem:580`, indreln premise): not a fuel'd definition
itself — the premise references the fuel-lifted `monStep` — so
`structural` has no site to attach to; it stays (C)/refused: the
concurrency model's restatement, outside the consumer's fragment (their
words), unchanged from the fuel-parameter record.

### 6.1 The table (67 rows; class as above; the condensed first error line)

| # | function (file) | class | refusal (first error line, condensed: `@l.N` = the call's source line) |
|---|---|---|---|
| 1 | `are_compatible` (`ail/ailTypesAux.lem`) | COMPUTED | parameter p: @l.809, arg not a variable; parameter p0: @l.809, arg not a variable |
| 2 | `are_compatible_params_aux` (`ail/ailTypesAux.lem`) | SIBLING | mutual sibling are_compatible refused (all-or-none) |
| 3 | `are_compatible_params` (`ail/ailTypesAux.lem`) | SIBLING | mutual sibling are_compatible refused (all-or-none) |
| 4 | `eq_core_base_type` (`core.lem`) | HOF | self-reference to eq_core_base_type in non-call position (passed as a value to a higher-order function) |
| 5 | `zeros_aux` (`core_aux.lem`) | UNTRACKED | parameter tagDefs1: @l.581, arg = the parameter itself; parameter c: @l.592, the argument `ty` not constructor-bound on it |
| 6 | `in_pattern` (`core_aux.lem`) | SAME | parameter sym1: @l.932, arg = the parameter itself; parameter g: @l.932, the call supplies fewer than 2 arguments |
| 7 | `subst_wait` (`core_aux.lem`) | UNTRACKED | parameter tid1: @l.1642, arg = the parameter itself; parameter v: @l.1642, arg = the parameter itself; parameter g: @l.1646, the argument `e` not constructor-bound on it |
| 8 | `find_labeled_continuation2_aux` (`core_aux.lem`) | UNTRACKED | parameter acc: @l.1808, the argument `acc'` not constructor-bound on it; parameter sym1: @l.1808, arg = the parameter itself; parameter g: @l.1808, the argument `e` not constructor-bound on it |
| 9 | `loadedValueFromMemValue` (`core_aux.lem`) | HOF | self-reference to loadedValueFromMemValue in non-call position (passed as a value to a higher-order function) |
| 10 | `memValueFromValue` (`core_aux.lem`) | UNTRACKED | parameter ty1: @l.186, the argument `elem_ty` not constructor-bound on it; parameter cval: @l.186, arg not a variable |
| 11 | `subst_sym_pexpr` (`core_aux.lem`) | UNTRACKED | parameter sym1: @l.950, arg = the parameter itself; parameter cval: @l.950, arg = the parameter itself; parameter g: @l.950, the argument `pe` not constructor-bound on it |
| 12 | `subst_sym_expr` (`core_aux.lem`) | UNTRACKED | parameter sym1: @l.1015, arg = the parameter itself; parameter cval: @l.1015, arg = the parameter itself; parameter g: @l.1021, the argument `e` not constructor-bound on it |
| 13 | `subst_pattern_val` (`core_aux.lem`) | UNTRACKED | parameter g: @l.1137, the argument `pat'` not constructor-bound on it; parameter cval: @l.59, arg not a variable; parameter expr1: @l.59, arg not a variable |
| 14 | `unsafe_subst_sym_pexpr` (`core_aux.lem`) | UNTRACKED | parameter sym1: @l.1222, arg = the parameter itself; parameter g: @l.1222, arg = the parameter itself; parameter g0: @l.1222, the argument `pe` not constructor-bound on it |
| 15 | `unsafe_subst_sym_expr` (`core_aux.lem`) | UNTRACKED | parameter sym1: @l.1287, arg = the parameter itself; parameter pe': @l.1287, arg = the parameter itself; parameter g: @l.1292, the argument `e` not constructor-bound on it |
| 16 | `unsafe_subst_pattern` (`core_aux.lem`) | UNTRACKED | parameter g: @l.1425, the argument `pat'` not constructor-bound on it; parameter pe': @l.1425, the argument `pe` not constructor-bound on it; parameter expr1: @l.59, arg not a variable |
| 17 | `subst_pattern` (`core_aux.lem`) | UNTRACKED | parameter g: @l.1509, the argument `pat'` not constructor-bound on it; parameter pe': @l.1509, the argument `pe` not constructor-bound on it; parameter expr1: @l.1498, arg = the parameter itself |
| 18 | `match_pattern` (`core_aux.lem`) | UNTRACKED | parameter g: @l.2030, the argument `pat'` not constructor-bound on it; parameter cval: @l.2023, arg not a variable |
| 19 | `to_pure` (`core_aux.lem`) | UNTRACKED | parameter g: @l.1533, the argument `e` not constructor-bound on it |
| 20 | `to_pures` (`core_aux.lem`) | SIBLING | mutual sibling to_pure refused (all-or-none) |
| 21 | `collect_saves_aux` (`core_aux.lem`) | HOF | self-reference to collect_saves_aux in non-call position (passed as a value to a higher-order function) |
| 22 | `m_collect_saves_aux` (`core_aux.lem`) | HOF | self-reference to m_collect_saves_aux in non-call position (passed as a value to a higher-order function) |
| 23 | `find_labeled_continuation` (`core_aux.lem`) | UNTRACKED | parameter sym1: @l.1716, arg = the parameter itself; parameter g: @l.1716, the argument `e` not constructor-bound on it |
| 24 | `update_env_aux` (`core_aux.lem`) | UNTRACKED | parameter g: @l.2445, the argument `pat'` not constructor-bound on it; parameter cval: @l.59, arg not a variable; parameter env1: @l.59, arg not a variable |
| 25 | `pull_constrained` (`core_eval.lem`) | UNTRACKED | parameter n: @l.200, arg not a variable; parameter g: @l.200, the argument `pe` not constructor-bound on it |
| 26 | `step_eval_pexpr` (`core_eval.lem`) | UNTRACKED | parameter n: @l.547, arg not a variable; parameter loc1: @l.547, arg = the parameter itself; parameter parent_call_loc_opt: @l.547, arg = the parameter itself; parameter core_extern1: @l.547, arg = the parameter itself; parameter env1: @l.547, arg = the parameter itself; parameter mem_st_opt: @l.547, arg = the parameter itself; parameter  |
| 27 | `eval_pexpr_aux2` (`core_eval.lem`) | UNTRACKED | parameter loc1: @l.1137, arg = the parameter itself; parameter current_call_loc_opt: @l.1137, arg = the parameter itself; parameter core_extern1: @l.1137, arg = the parameter itself; parameter env1: @l.1137, arg = the parameter itself; parameter mem_st_opt: @l.1137, arg = the parameter itself; parameter file1: @l.1137, arg = the parameter |
| 28 | `eval_pexpr_aux_broken` (`core_eval.lem`) | UNTRACKED | parameter loc1: @l.1189, arg = the parameter itself; parameter current_call_loc_opt: @l.1189, arg = the parameter itself; parameter core_extern1: @l.1189, arg = the parameter itself; parameter env1: @l.1189, arg = the parameter itself; parameter mem_st_opt: @l.1189, arg = the parameter itself; parameter file1: @l.1189, arg = the parameter |
| 29 | `one_step_unseq_aux` (`core_reduction.lem`) | COMPUTED | parameter p: @l.262, arg not a variable |
| 30 | `has_ccall` (`core_reduction.lem`) | HOF | self-reference to has_ccall in non-call position (passed as a value to a higher-order function) |
| 31 | `get_ctx` (`core_reduction.lem`) | CROSS-CALL | parameter g: sibling call @l.548: no consistent structural position |
| 32 | `get_ctx_unseq_aux` (`core_reduction.lem`) | SIBLING | mutual sibling get_ctx refused (all-or-none) |
| 33 | `full_eval_pexpr` (`core_reduction.lem`) | UNTRACKED | parameter th_st: @l.58, arg = the parameter itself; parameter core_extern1: @l.58, arg = the parameter itself; parameter mem_st: @l.58, arg = the parameter itself; parameter file1: @l.58, arg = the parameter itself; parameter pe: @l.58, the argument `pe'` not constructor-bound on it |
| 34 | `add_to_sb` (`core_run_aux.lem`) | UNTRACKED | parameter p_aids: @l.353, arg = the parameter itself; parameter g: @l.353, the argument `e` not constructor-bound on it |
| 35 | `add_to_asw` (`core_run_aux.lem`) | UNTRACKED | parameter aids: @l.444, arg = the parameter itself; parameter g: @l.444, the argument `e` not constructor-bound on it |
| 36 | `convert_pexpr` (`core_run_aux.lem`) | HOF | self-reference to convert_pexpr in non-call position (passed as a value to a higher-order function) |
| 37 | `convert_expr` (`core_run_aux.lem`) | HOF | self-reference to convert_expr in non-call position (passed as a value to a higher-order function) |
| 38 | `ctypeEqual` (`ctype.lem`) | UNTRACKED | parameter c: @l.159, the argument `ty1` not constructor-bound on it; parameter c0: @l.159, the argument `ty2` not constructor-bound on it |
| 39 | `are_compatible_aux` (`ctype_aux.lem`) | COMPUTED | parameter env1: @l.200, arg = the parameter itself; parameter acc: @l.200, arg not a variable |
| 40 | `are_compatible_params_aux` (`ctype_aux.lem`) | SIBLING | mutual sibling are_compatible_aux refused (all-or-none) |
| 41 | `are_compatible_params` (`ctype_aux.lem`) | SIBLING | mutual sibling are_compatible_aux refused (all-or-none) |
| 42 | `has_concurRead` (`defacto_memory.lem`) | HOF | self-reference to has_concurRead in non-call position (passed as a value to a higher-order function) |
| 43 | `find_array_index` (`defacto_memory.lem`) | COMPUTED | parameter size: @l.2180, arg = the parameter itself; parameter i: @l.2180, arg not a variable; parameter ival_: @l.2180, arg = the parameter itself |
| 44 | `easy_update_mem_value_aux` (`defacto_memory.lem`) | SAME | parameter loc1: @l.2194, arg = the parameter itself; parameter is_strong: @l.2194, arg = the parameter itself; parameter write_ty: @l.2194, the call supplies fewer than 3 arguments; parameter sh: @l.2194, the call supplies fewer than 4 arguments; parameter write_mval: @l.2194, the call supplies fewer than 5 arguments; parameter current_mv |
| 45 | `memcmp_load_aux` (`defacto_memory.lem`) | COMPUTED | parameter ptrval: @l.2591, arg = the parameter itself; parameter offset: @l.2591, arg not a variable; parameter max_offset: @l.2591, arg = the parameter itself; parameter acc: @l.2591, arg not a variable |
| 46 | `mkUnspec` (`defacto_memory.lem`) | UNTRACKED | parameter c: @l.433, the argument `ty` not constructor-bound on it |
| 47 | `tmp_compl_aux` (`defacto_memory_aux.lem`) | UNTRACKED | parameter nbits: @l.124, arg not a variable; parameter n: @l.124, the argument `n_` not constructor-bound on it |
| 48 | `tmp_AND_aux` (`defacto_memory_aux.lem`) | UNTRACKED | parameter nbits: @l.138, arg not a variable; parameter n1: @l.138, the argument `n1_` not constructor-bound on it; parameter n2: @l.138, the argument `n2_` not constructor-bound on it |
| 49 | `tmp_OR_aux` (`defacto_memory_aux.lem`) | UNTRACKED | parameter nbits: @l.148, arg not a variable; parameter n1: @l.148, the argument `n1_` not constructor-bound on it; parameter n2: @l.148, the argument `n2_` not constructor-bound on it |
| 50 | `tmp_XOR_aux` (`defacto_memory_aux.lem`) | UNTRACKED | parameter nbits: @l.159, arg not a variable; parameter n1: @l.159, the argument `n1_` not constructor-bound on it; parameter n2: @l.159, the argument `n2_` not constructor-bound on it |
| 51 | `fake_mem_value_eq` (`defacto_memory_aux.lem`) | HOF | self-reference to fake_mem_value_eq in non-call position (passed as a value to a higher-order function) |
| 52 | `simplify_integer_value_base` (`defacto_memory_aux.lem`) | UNTRACKED | parameter ival_: @l.189, the argument `x` not constructor-bound on it |
| 53 | `print_eval_conv_aux` (`driver.lem`) | UNTRACKED | parameter dr_st: @l.122, arg = the parameter itself; parameter th_st: @l.122, arg = the parameter itself; parameter pe: @l.122, the argument `pe` not constructor-bound on it |
| 54 | `drive_nonmemory_steps_aux2` (`driver.lem`) | COMPUTED | parameter acc: @l.1077, arg not a variable |
| 55 | `driver2` (`driver.lem`) | HOF | self-reference to driver2 in non-call position (passed as a value to a higher-order function) |
| 56 | `hack` (`driver.lem`) | UNTRACKED | parameter core_extern1: @l.1454, arg = the parameter itself; parameter env1: @l.1454, arg = the parameter itself; parameter mem_st: @l.1454, arg = the parameter itself; parameter core_file1: @l.1454, arg = the parameter itself; parameter concur_sym_map: @l.1454, arg = the parameter itself; parameter pexpr1: @l.1454, the argument `pexpr'`  |
| 57 | `showNonNegativeWithBasis_aux` (`formatted.lem`) | UNTRACKED | parameter acc: @l.321, arg not a variable; parameter useUpper: @l.321, arg = the parameter itself; parameter b: @l.321, arg = the parameter itself; parameter n: @l.321, the argument `r` not constructor-bound on it |
| 58 | `load_character_array_aux` (`formatted.lem`) | UNTRACKED | parameter elem_ty: @l.384, arg = the parameter itself; parameter ptrval: @l.384, the argument `ptrval'` not constructor-bound on it; parameter prec_n_opt: @l.384, the argument `prec_n_opt'` not constructor-bound on it; parameter acc: @l.384, arg not a variable |
| 59 | `many` (`monadic_parsing.lem`) | CROSS-CALL | parameter p: sibling call @l.48: no consistent structural position |
| 60 | `many1` (`monadic_parsing.lem`) | SIBLING | mutual sibling many refused (all-or-none) |
| 61 | `nd_bind` (`nondeterminism.lem`) | UNTRACKED | parameter n: @l.70, the argument `m` not constructor-bound on it; parameter f1: @l.70, arg = the parameter itself |
| 62 | `liftND` (`nondeterminism.lem`) | CROSS-CALL | parameter get2: sibling call @l.279: no consistent structural position; parameter put1: sibling call @l.279: no consistent structural position; parameter liftInfo: sibling call @l.279: no consistent structural position; parameter liftErr: sibling call @l.279: no consistent structural position; parameter n: sibling call @l.279: no consiste |
| 63 | `liftAction` (`nondeterminism.lem`) | SIBLING | mutual sibling liftND refused (all-or-none) |
| 64 | `mkListN_aux` (`utils.lem`) | COMPUTED | parameter n: @l.27, arg = the parameter itself; parameter i: @l.27, arg not a variable; parameter acc: @l.27, arg not a variable |
| 65 | `mkListFromTo_aux` (`utils.lem`) | COMPUTED | parameter i: @l.36, arg not a variable; parameter max2: @l.36, arg = the parameter itself; parameter acc: @l.36, arg not a variable |
| 66 | `replicate_list_` (`utils.lem`) | COMPUTED | parameter x: @l.188, arg = the parameter itself; parameter n: @l.188, arg not a variable; parameter acc: @l.188, arg not a variable |
| 67 | `list_unfoldr_aux` (`utils.lem`) | UNTRACKED | parameter acc: @l.299, arg not a variable; parameter ctor1: @l.299, arg = the parameter itself; parameter b0: @l.299, the argument `b'` not constructor-bound on it |


## 7. Gates — verbatim

Each commit was gated on its own tree (the gate is `tests/comprehensive`
`make lean`, all phases, clean — generated files, `lean-test` links and
the parity outputs removed first; `lean` never rebuilt during a run —
the one run where it was (`.tmp/gate1.log`) failed its negative phase for
that reason alone and was discarded).

### 7.1 `make lean` on `d8bbb4e` (the declare; `.tmp/gate3.log`)

```
=== Generation: 48 passed, 0 failed, 0 skipped ===
Build completed successfully (139 jobs).
  OK (leg 1): panic prints the Incomplete Pattern message, then continues with default
  OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1
single-evaluation: OK
  OK: compiled draw sequences hold
  OK: compiled consumer injection holds
  OK (leg 1): two sufficient fuels agree; insufficient gives the declared sentinel; callee starts from the full ambient
  OK (leg 2): loud exhaustion at an insufficient runtime fuel fail-stops (exit 134)
  [56 × "OK (rejected as declared)" — derived count; the 11 neg_structural_* among them]
  OK: inv_fuel.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_reader_consumer.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_structural.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_supply.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
=== p_structural ===
  OK: parity (7 lines byte-identical to the OCaml reference; pin matches)
  [parity: 22 × "OK: parity", 7 × "OK: both fail", 3 × XFAIL (the registered f_int_of_big_num, p_str_bytes, p_str_escapes) — derived counts]
  OK: 224 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make lean  308.97s user 20.52s system 94% cpu 5:48.82 total
EXIT 0
```

### 7.2 `make lean` on `3c1846b` (D4; `.tmp/gate4.log`)

```
=== Generation: 48 passed, 0 failed, 0 skipped ===
Build completed successfully (139 jobs).
  [pins as in 7.1; 56 negatives OK; 4 invariance OK; parity 22 OK / 6 both-fail / 4 XFAIL — derived]
  OK: 224 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make lean  473.23s user 62.62s system 111% cpu 7:59.63 total
EXIT 0
```

### 7.3 `make lean` on `76b76da` (the exemplar; `.tmp/gate5.log`)

```
=== Generation: 48 passed, 0 failed, 0 skipped ===
Build completed successfully (140 jobs).
  [pins as in 7.1; 56 negatives OK; 4 invariance OK; parity 22 OK / 6 both-fail / 4 XFAIL — derived]
  OK: 224 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make lean  276.03s user 19.14s system 94% cpu 5:13.38 total
EXIT 0
```

### 7.4 lean-lib (after D4)

`lake build` (capped): `Build completed successfully (37 jobs).`;
`grep -rn "^axiom " . --include='*.lean'` in `lean-lib/`: 0 hits.
Kernel pins' axiom lines (build output, verbatim):
`'TestStructuralCheck.len_append' depends on axioms: [propext, Quot.sound]`,
`'TestStructuralCheck.rev_acc_length' depends on axioms: [propext, Quot.sound]`,
`'TestFuelMonoExemplar.spin_stable' depends on axioms: [propext]`,
`'TestFuelMonoExemplar.spin_fuel_irrelevant' depends on axioms: [propext]`.

### 7.5 tests/nonlean-regress

On `d8bbb4e` (declare only), verbatim:
`nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)`
— the new declare changes no non-Lean output (the `{lean}` echo only
appears in sources that use it, none of which is in the net's corpus).

On the D4 tree BEFORE rebaseline: `nonlean-regress: FAIL — non-Lean
emitter output changed`; 27 rows drifted (`-`/`+` pairs), by emitter
(derived): `backends/tex_all` 20, `lib/tex_all` 2, `lib/tex` 2, `lib/lem` 1,
`lib/ident.stdout` 1, `lib/html` 1 — every one a HUMAN/ECHO rendering of
`library/num.lem`'s four changed `declare lean target_rep` lines
(`tex_all` renders the library into every test's artifact); NO
`ocaml`/`hol`/`isa`/`coq` row; `golden.exitcodes` unchanged. Rebaselined
under the net's protocol (a reviewed, intended library edit;
`NONLEAN_REGRESS_REBASELINE=1`, `REBASE EXIT 0`; `golden.sha256` rows
changed 54 = 27 pairs, exitcodes diff 0), then re-run, verbatim:
`nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)`.

## 8. OCaml byte-identity — verbatim

Baseline lem = the `9ba8970` binary (`.tmp/lem-base`, rebuilt from that
source in this worktree, `Lem 9ba8970`); this lem = `Lem 9ba8970-dirty`
at `d8bbb4e`'s source (the D4 commit touches no emitter).

1. **Comprehensive corpus** (`tests/comprehensive/test_*.lem` + parity
   probes + invariance sources, `-ocaml`, `LEMLIB` = this tree's
   library): `ml files: base=105 new=111`; `diff -r` prints ONLY
   `Only in .tmp/ocaml-new: …` for the six `.ml` of the four sources
   that carry the new declare (`test_structural`, `p_structural`,
   `inv_structural`, `test_contextual_keywords` and two auxiliaries —
   the baseline lem cannot parse `declare {lean} structural`, exit 1 vs
   0 in the exit lists); every one of the 105 pre-existing `.ml` files
   is byte-identical.
2. **The cerberus tree** (`frontend/` of cerberus-lean primary @
   `1b57bcf26`, copied to `.tmp/cerb-ocaml`, the five numeric fuel lines
   deleted so both lems accept it, `LEM_SRC` = 86 files from the cerberus
   Makefile via `make --eval`, the Makefile's flags, both lems run with
   `LEMLIB` set), verbatim:
   ```
   base exit 0
   new exit 0
   files: base=86 new=86
   OCAML DIFF exit 0 lines 0
   ```

## 9. Decisions for the operator

- **Monotonicity vocabulary (row 13).** Whether to add a declared
  absorbing-outcome/monad surface (Route A) or fund the body
  instrumentation (Route B) — both L; the exemplar fixes the target
  shape; the consumer said the first pin does not need generation.
- **`structural` on a non-recursive def is REFUSED** [AGENT] (an inert
  declare is refused, as FC-inert is). If the operator prefers
  accept-as-no-op for cerberus's convenience (a declare surviving a
  refactor that removes the recursion), it is a one-line change and the
  probe flips.
- **The nonlean-regress goldens** were REBASELINED for the D4 library edit (§7.5: 27
  human/echo rows, no semantic emitter row) [AGENT] under the net's own
  protocol ("rebaseline ONLY for a reviewed, intended output change") —
  the change is the ruled D4; the operator may want to eyeball the
  `lib/lem/num-processed.lem` row (four `declare lean target_rep` lines).

## 10. Not done, and why

- **Monotonicity generation** (row 13): not built — L on both routes
  (§5); the exemplar and the specification are in the tree.
- **The census's Lean phase** had no work: 0/67 passed generation as
  written, so Lean's checker adjudicated nothing except the D2
  demonstration (§6). The driver `census_lean.py` exists in `.tmp/` and is
  described here; it is not committed (scratch).
- **The Ott grammar** carries the new row; derived artifacts not
  regenerated (TODO row 5, pre-existing).
- **`.tmp/`** (baseline binary, scratch trees, the census copies ~2 GB,
  logs) is ephemeral and deleted at slice end; everything load-bearing is
  quoted above.
