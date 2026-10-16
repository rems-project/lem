# Fuel-parameter arc — lem half, record (2026-09-04)

Branch `arc/fuel-parameter` (lem-lean), base mainline `mdd/lean-backend`
@ `0890229` + the design note (`774569c`) + the operator's general form
(`0db35ec`). Charter: `2026-09-03_fuel-parameter-design.md` (§4 lists the
questions settled here; its R1 section carries the deltas from the
draft). Worker [AGENT] (lem-lean); rulings [USER 2026-09-03] paraphrased;
every quoted output is verbatim from this tree; tallies marked
"derived" are derived. Nothing merged, nothing pushed.

## 0. Commits

| Commit | Content |
|---|---|
| `d80505b` | Backend: fuel is the `[LemFuel]` instance (fuel lifting = the reader fixpoint with an instance-implicit binder); numeric budgets + `lemDefaultFuel` deleted; `fuel_consumer` declare; generated `f_lemFuel_zero` lemmas; fuel scope net; gate; tests; manual/DESIGN/README; design note R1 |
| `b18715f` | Zero lemma also for typed/parenthesised parameter patterns (cerberus: 67/67) |
| `16fe2ff` | LemLib: `Pset.join`/`Pmap.join` height-indexed structural (kernel-computable); `heightsOk`; `join_eq` theorems; closed-term `decide` tests |
| `22a2b17` | LemLib: `natFromNatural`/`intFromInteger` identity (63-bit OCaml checks removed); `f_int_of_big_num` a ruled OCaml-target deviation; X3 addendum |
| (this record's commit) | record, TODO rows 10–14 |

## 1. The rulings this slice implements

- [USER 2026-09-03]: fuel is an execution parameter whose value does not
  matter — any fuel value can be chosen; this and all other magic values
  are completely forbidden; fuel is a parameter chosen by the caller of
  the interpreter (10^8 or any other value). All similar magic values
  are to be removed and replaced by quantified parameters. The LemLib
  bounds are fine if they are passed to the semantics as parameters that
  a calling context can choose; otherwise they are forbidden magic
  values.
- General form [USER 2026-09-03]: any value that a context or theorem can
  quantify over is fine; defaults chosen e.g. in test suites are fine;
  any hardcoded magic value that cannot be quantified over is by
  definition a bug, unless it mirrors a lem or ISO-C design choice.
- Third form [USER 2026-09-03]: the aim is to forbid values that limit the
  semantics or limit the ways the customer can reason about the
  semantics, and the proposal did not seem to do that — structural
  recursion on a DATA measure is admissible.
- [USER 2026-09-03]: OCaml limits hardcoded because of OCaml-level
  execution issues are forbidden as well; the logical semantics is what
  counts.

Every value touched below is classified against the general form: a
caller parameter (quantifiable), a test-suite choice (fine), a data
measure / termination proof (nothing chosen), lem's own semantics (not
magic), or an OCaml-execution limit (forbidden).

## 2. Design decisions (the design note's §4, plus what the build forced)

**§4.1 Mechanism — the ambient fuel is a LemLib class, taken as an
instance-implicit binder.** `class LemFuel where fuel : Nat`
(`lean-lib/LemLib.lean`). A fuel'd `f` emits the total worker
`f_lemFuel (lemFuel : Nat) …` (unchanged), the wrapper
`def f [LemFuel] : T := f_lemFuel LemFuel.fuel`, and the lemma
`theorem f_lemFuel_zero … : f_lemFuel 0 … = <sentinel> := rfl`. Every
definition that (transitively) reaches a fuel'd constant, a fuel-lifted
definition or a `{lean} fuel_consumer` takes `[LemFuel]`
(`lean_fuel_prepass`, `src/lean_backend.ml`: the reader-lifting fixpoint
at `Val_def` granularity, instances skipped, `reader_seed` defs INCLUDED,
target_rep'd defs excluded). Call sites are textually unchanged (instance
resolution passes the binder); bare/HOF references need no repair; the
entry point supplies `@f ⟨n⟩ …` or `letI : LemFuel := ⟨n⟩`; a theorem
quantifies `∀ [LemFuel]` or over `n` (`@f ⟨n⟩ = f_lemFuel n` by rfl).

Reasons, and the alternatives rejected: (a) an explicit `(_lemFuel : Nat)`
reader-style binder threaded at every call site — built first
(0db35ec-dirty, not committed): it changed the text of every call of a
fuel'd function, needed the partial-application repair for HOF uses, and
needed an injection rule for hand-written reps; the consumer's first
requirement ("a single parameter — module-level or a typeclass-style
instance argument — not per-signature threading") rules it out. (b)
folding fuel into the reader parameter list — couples fuel to
`reader_seed` (one seed argument cannot seed two ambients) and gives a
reader-only def a fuel binder. (c) a module-level `variable [LemFuel]` —
Lean includes section variables by header mention only; fragile and
per-file. (d) a global `opaque`/constant fuel — not quantifiable: the
defect itself. A hazard the class form has that (a) has not: a stray
global `instance : LemFuel` would silently give every fuel'd function a
default; the gate (§8.4) forbids one in LemLib and in generated code.

**A worker takes `[LemFuel]` only when it passes the ambient on.** The
block's bodies are scanned for fuel outside the block (`workers_need_fuel`,
all-or-none per `let rec … and` block, like the counter); a leaf worker's
only fuel is its counter, so its theorems carry no instance. Every fuel'd
callee starts from the FULL ambient, never from the caller's remaining
counter (the design note's §3 sentence; pinned by
`TestFuelParamCheck` (5): `@outer ⟨4⟩ 3 = 0`).

**§4.2 Hand-written reps that call `_lemFuel` workers: `declare {lean}
fuel_consumer val f`.** The rep's implementation takes `[LemFuel]` and
reads `LemFuel.fuel`; the declare makes its callers fuel-lifted; call
sites are unchanged (guards FC-rep: must carry a Lean target_rep;
FC-inert: a fuel SENTINEL on a rep'd val is refused). For cerberus: each
`mem.lem` consumer whose `CerbMem` implementation reaches a `_lemFuel`
worker gets `declare {lean} fuel_consumer` beside its `reader_consumer`,
and the implementation replaces `lemDefaultFuel` by `LemFuel.fuel` (§6).
The draft's "the memory model's ambient record carries it" was rejected:
it makes two fuels (the record's and the generated code's).

**§4.3 A fuel'd function referenced with no ambient fuel in scope** —
a lem `assert`, an indreln rule, an instance method — is a generation-
time error naming the site (`fuel_scope_check` at the three reference
sites; the instance guard mirrors the reader lifting's). There is no
default to inject, by design. A LIBRARY assert renders as a
removed-comment instead (the library's `_auxiliary.lean` files are
deleted by `make lean-libs`; measured on relation.lem's
`withoutTransitiveEdges` rows while the caller-fuelled `tc` variant was
built). Consequence measured on cerberus: three `Eq` instances and one
indreln rule hit the guard (§6) — an OPERATOR/consumer decision (§9).

**§4.4 Perf** — §7.

**§4.5 LemLib** — §4 (table).

**Deleted** (the defect itself): the numeric form `declare {lean} fuel
val f = N` — the parser production is kept only to refuse it with its
reason (`Parse_error_locn`, negative `neg_fuel_numeric_budget`; a bare
syntax error would not say why); `const_descr.fuel_budget` (replaced by
`fuel_consumer : Targetset.t` — one field out, one in), `Decl_fuel_budget`
/ `Decl_fuel_budget_decl` (→ `Decl_fuel_consumer`), the human-target echo
of the budget, `lean_fuel_budget_check`, `lean_fuel_budget_completeness_check`,
`fuel_budget_for`, the `lemDefaultFuel` reserved-def-name guard (the name
has no meaning to the backend any more; `LemFuel` joins
`library/lean_constants` so a user type/def of that name is renamed);
`def lemDefaultFuel : Nat := 1000000` (LemLib HISTORY note remains);
`test_fuel_budget.lem`, `TestFuelBudgetExec.lean`, phase
`lean-fuel-budget`, `neg_fuel_budget_{nosentinel,rep,speconly,zero}.lem`,
`neg_default_fuel_name.lem`, `inv_fuel_budget.lem` (→ `inv_fuel.lem`);
the `fuel_draws_b` budget rows of `test_supply.lem`, `p_supply_shapes`
(pin edited: the OCaml reference row removed, runner confirms the pin
matches), `TestSupplyCheck/Draws`. Grammar: `language/lem.ott` row
`fuel_budget_decl` → `fuel_consumer_decl`. ocamlyacc at the final
grammar, verbatim: `5 rules never reduced` / `2 shift/reduce conflicts,
2 reduce/reduce conflicts.` — unchanged from the baseline.

## 3. Before / after — one fuel'd function, verbatim

`tests/comprehensive/test_target_reps.lem`, ``declare {lean} fuel val
fuel_countdown = `999` `` and its caller. BEFORE (lem `0db35ec`,
`Test_target_reps.lean:459-468`):

```lean
 def  fuel_countdown_lemFuel (lemFuel : Nat)  (n : Nat)  : Nat := match lemFuel with
  | 0 => (999)
  | Nat.succ lemFuel => (
  if  n  ==   0 then   0  else (fuel_countdown_lemFuel lemFuel)  (n  -   1))

def fuel_countdown : Nat → Nat := fuel_countdown_lemFuel lemDefaultFuel

def  uses_countdown   (k  : Nat)   :  Nat :=  fuel_countdown  k  +   1
```

AFTER (this lem, `Test_target_reps.lean:459-470`):

```lean
 def  fuel_countdown_lemFuel (lemFuel : Nat)  (n : Nat)  : Nat := match lemFuel with
  | 0 => (999)
  | Nat.succ lemFuel => (
  if  n  ==   0 then   0  else (fuel_countdown_lemFuel lemFuel)  (n  -   1))

def fuel_countdown [LemFuel] : Nat → Nat := fuel_countdown_lemFuel LemFuel.fuel
theorem fuel_countdown_lemFuel_zero ( n : Nat) :
    fuel_countdown_lemFuel 0  n = (999) := rfl

def  uses_countdown [LemFuel]   (k  : Nat)   :  Nat :=  fuel_countdown  k  +   1
```

The worker is byte-identical; the wrapper's numeral became the ambient;
the caller gained the binder and nothing else. A worker that passes the
ambient on (cerberus `driver2_lemFuel`, `outer_lemFuel` in
`test_fuel_param.lem`) reads `def driver2_lemFuel [LemFuel] (lemFuel : Nat) …`.

## 4. LemLib — every bounded recursion, classified (the operator's aim as the test)

Test: "forbid values that limit the semantics or limit the ways the
customer can reason about the semantics". Forms: (a) caller parameter,
(b) termination proof (well-founded), (c) data-measure structural
recursion.

| Function (`lean-lib/LemLib.lean`) | Before | Now | Form | Theorem |
|---|---|---|---|---|
| `lemDefaultFuel` | `1000000` | DELETED | — (was magic) | — |
| `Pset.join`, `Pmap.join` | WF on `sizeOf l + sizeOf r` | `joinGo` indexed by `height l + height r + 1` | (b) → (c): kernel-computable | `LemLibTheorems.PsetJoin.join_eq`, `PmapJoin.join_eq` (under `heightsOk`; axioms `[propext, Classical.choice, Quot.sound]`) |
| `Pset.unionGo/interGo/diffGo/subsetGo`, `Pmap.mergeGo` | index `height s1 + height s2 + 1` | unchanged, reclassified | (c) | none needed (no rewrite) |
| `Pset.compareAux`, `Pmap.equalAux`, `Pmap.compareAux` | index `cardinal s1 + cardinal s2 + 1` | unchanged, reclassified | (c) | none needed |
| `Pset.tc` | `lfpGo … ((2n)(2n) + 1)` | unchanged, reclassified; a caller-fuelled variant via `fuel_consumer` on `Relation.transitiveClosureByCmp` was BUILT and WITHDRAWN (§9 D1) | (c) — flagged | — |
| `Pset.lfpGo` | fuel-taking primitive | unchanged; documented as the caller-fuelled primitive whose one caller (`tc`) supplies a data measure | (a) | — |
| `lemLeastFixedPoint` | `bound` from lem, `\| 0 => x` silent | unchanged | lem's own `Set.leastFixedPoint` (set.lem:709 `\| 0 -> x`) — a lem design choice, exempt by rule (§9 D3, resolved) | — |
| `gen_pow_aux`, `listSet`, `boolListFromNatural`, `bitSeqBinopAux`, `lemStringFromNatHelper`, `lemStringFromNaturalHelper` | WF (`exp`, `remainder`, list lengths, `n`) | unchanged | (b) — admissible; blocks kernel computation like `join` did | TODO row 12 |
| `natFromNatural` / `intFromInteger` | fail outside ±2^62 (OCaml limit) | identity | OCaml-execution limit REMOVED | — |

`Pset.heightsOk`/`Pmap.heightsOk` (Bool) are new: the invariant the
height index relies on, and the predicate the consumer's Pmap-laws slice
builds on. Zero-axiom census: `grep -rn "^axiom " lean-lib/ --include="*.lean"`
→ no hits (exit 1). Kernel-only methods throughout (`rfl`, `decide`,
`omega`, `simp`); no `native_decide`, no heartbeat/maxRecDepth option
anywhere. Kernel-computability evidence (scratch, verbatim):
`Pset.elements (Pset.join cNat (Pset.fromList cNat [1, 2]) 3 (Pset.fromList cNat [4, 5, 6, 7])) = [1, 2, 3, 4, 5, 6, 7] := by decide`
succeeds; the same over `PsetJoin.joinSpec` (the WF form): "Tactic
`decide` failed for proposition … did not reduce to `isTrue` or
`isFalse`". `LemLibTest.lean` decides closed terms through
`Pset.union/inter/diff/remove`, `Pmap.union/remove`, `fmapUnionBy`,
`fmapDeleteBy`.

## 5. Exhaustion and monotonicity (consumer requirements 2–3)

Generated: `f_lemFuel_zero` for every fuel'd function whose parameters
are variables, `(x : t)` annotations, parenthesised variables or
wildcards — lem's pattern compiler makes them so (a source `let rec f
(a, b) = …` arrives as `f p = match p with …`); the "not generated"
comment path is a backstop no lem source reached (cerberus: 67/67, §6).
The statement mirrors the worker's `| 0 =>` arm through one shared
renderer (`fuel_sentinel_output`), supply pairing included, so the two
agree by construction.

NOT generated — monotonicity ("completes at fuel f ⇒ identical at every
f' ≥ f"). What is true today: the unfolding equations `f_lemFuel.eq_1/2`
exist for every worker, and above the depth a program needs the value
is fuel-independent — a per-function, per-argument fact
(`TestFuelParamCheck.spin_sufficient`/`spin_fuel_irrelevant` show the
shape). What blocks a generic or generated theorem: (i) with the
convention's payload `fuelExhausted x` the sentinel is an OPAQUE value,
so "`f_lemFuel n x ≠ payload`" is not statable, let alone provable; (ii)
even with a distinguished value payload (`999`, cerberus's
`NDkilled fuelExhaustedKill`), "result ≠ payload at n ⇒ same result at
n+1" is FALSE in general — a body may absorb a sub-call's sentinel
(`if f (n-1) = 999 then 0 else …`) and change value once the sub-call
completes. Monotonicity is a property of how the body CONSUMES
exhaustion, not of the scheme. What it requires: an exhaustion outcome
that the return type distinguishes AND that every consumer of a recursive
result propagates (an absorbing element of the monad — cerberus's
`NDkilled` through `nd_bind` is exactly that); then the per-function
lemma follows by induction on the counter, and the backend could
generate it for functions whose payload is a DECLARED absorbing outcome
of a DECLARED monad — new vocabulary, an operator decision (TODO row 13).

## 6. Cerberus dry run (read-only; scratch copy of `frontend/**/*.lem` at cerberus-lean primary `de2fbf1bd`)

Method: `.tmp/cerb/run.sh` — the cerberus Makefile's exact flags
(`-wl ign -wl_rename warn -wl_pat_red err -wl_pat_exh warn -cerberus_pp`)
and its expanded `LEM_SRC` (86 files) / `LEM_SRC_LEAN` (85), obtained
with `make --eval` (read-only; the record's first draft said 87/86 — it
had counted the echoed command word, audit N3); OCaml with the baseline lem (`0db35ec`,
saved binary) and with this lem; Lean with this lem.

1. **The five numeric declares are refused on every target**
   (`driver.lem:1915-1918` `print_eval_conv_aux`,
   `drive_nonmemory_steps_aux2`, `driver2`, `hack` = 100000000;
   `nondeterminism.lem:574` `nd_bind` = 100000000), verbatim: `Syntax
   error: the numeric fuel-budget form 'declare {lean} fuel val f = N'
   was removed (fuel-parameter arc, 2026-09-04) …`. The cerberus half
   DELETES those five lines (fail-closed: `lem` refuses the sources until
   it does; the sentinel declares on the same five vals stay).
2. **OCaml byte-identity.** Same sources (the scratch copy with the five
   lines deleted), baseline lem vs this lem: `files: base=86 new=86` /
   `OCAML DIFF exit 0 lines 0` (`diff -r`, verbatim). Baseline lem on the
   ORIGINAL sources vs this lem on the edited sources: one hunk,
   `driver.ml:2308a2309,2313`, a 5-line source comment (`(* FUEL arc budget
   commit … *)`) that the original's `declare` line SWALLOWED — non-human
   targets emit `emp` for a `{lean}` declare, leading skips included — and
   that now attaches to the next definition. Not a backend change; a
   pre-existing quirk of every `{lean}` declare, noted.
3. **Lean generation** succeeds (`new-lean exit 0`, 170 files) once four
   more source sites are addressed — measured by patching the SCRATCH
   copy only, each recorded:
   - `ctype.lem:183` `instance (Eq ctype) let (=) = ctypeEqual` — fuel'd
     equality as an instance method (error: "fuel'd (or fuel-lifted) call
     inside an instance method");
   - `core.lem:91-92` `instance (Eq core_base_type)` via `eq_core_base_type`;
   - `defacto_memory_aux.lem:38-39` `instance (Eq mem_value)` via
     `fake_mem_value_eq`;
   - `cmm_op.lem:580` indreln rule `monStep`: premise
     `Nondeterminism.mem ((a: action), z) (monStep pre y)` references the
     fuel-lifted `monStep` (error: "referenced outside a fuel scope").
   These are the §9 D2 decision (instance-level `[LemFuel]` in the
   backend vs restructuring in the model).
4. **Counts on the complete tree (derived, `grep`; recounted after audit
   N3):** `declare {lean} fuel val` rows over `LEM_SRC_LEAN` at
   `de2fbf1bd`: **72 in 15 files** (utils 4, ctype 1, ctype_aux 3,
   formatted 2, defacto_memory_aux 6, defacto_memory 5, monadic_parsing 2,
   nondeterminism 4, core 1, core_aux 20, ail/ailTypesAux 3, core_run_aux
   4, core_eval 4, core_reduction 5, driver 8), of which 5 numeric and
   **67 sentinel** — the first draft's "69 declares / 64 vals" was
   mis-derived (a `grep` over `frontend/model/*.lem` only, minus a comment
   line); 67 sentinel declares = 67 wrappers = 67 `_zero` lemmas, consistent;
   wrappers at the ambient
   `:= f_lemFuel LemFuel.fuel` **67 in 15 files** (the design note's
   "77 sites in 16 files" was a grep for `lemDefaultFuel` over cerberus's
   `lean_frontend/generated/`, which also holds the hand-written copies —
   `CerbMem.lean` alone has 12 such sites; measured today on that tree:
   73 `_lemFuel lemDefaultFuel` occurrences in 15 files); `f_lemFuel_zero`
   lemmas **67**, "not generated"
   0; definitions taking `[LemFuel]` **370**; workers passing the ambient
   26, leaf workers 41; literal fuels after `_lemFuel` **0**;
   `lemDefaultFuel` **0**.
5. **The six sealed recursions the consumer named**, each now
   fuel-parametric (verbatim heads from the generated tree):
   `def driver2 [LemFuel] : … := driver2_lemFuel LemFuel.fuel` (the
   scheduler loop; `theorem driver2_lemFuel_zero [LemFuel] …`);
   `def drive_nonmemory_steps_aux2 [LemFuel] …` (the single-thread loop;
   its `_zero` lemma states the kill: `… = (fun _ => ND (fun st =>
   (NDkilled (Error0 CerbFuel.fuelExhaustedLoc CerbFuel.fuelExhaustedMsg),
   st))) := rfl`); `def hack [LemFuel] …` (the exit routine);
   `def print_eval_conv_aux [LemFuel] …` (the printing helper);
   `def nd_bind {a b c d e f : Type} [LemFuel] : ndM f b d a c → …`
   (the monad's bind; leaf worker, so `nd_bind_lemFuel_zero` has no
   instance); the expression-step recursions `step_eval_pexpr`,
   `eval_pexpr_aux2`, `full_eval_pexpr` (formerly at `lemDefaultFuel`):
   all `[LemFuel]` with `_zero` lemmas. `drive` is hand-written
   (`CerbND.lean:450`) and follows in the seam edit.
6. **Hand-written seams to change (the cerberus half's brief), file:line
   at cerberus-lean `HEAD`:**
   - `lean_frontend/CerbMem.lean` `lemDefaultFuel` call sites: `:483`
     (`memberAlign`), `:489` (`offsetsofMembers`), `:494` (`offsetsof`),
     `:498` (`sizeofCtype`), `:502` (`alignofCtype`), `:691`
     (`memValueToBytes`), `:849-850` (`memValueToBytes_eq_append` corollary),
     `:1016` (`reconstructValue`), `:1155-1156` (corollary), `:1183`
     (`typeofMval`), `:1215` (`unqualifyAndUnatomic`): each entry takes
     `[LemFuel]` and passes `LemFuel.fuel` to its `_lemFuel` worker; the
     `mem.lem` consumers whose implementations reach them
     (`sizeof_ival`/`alignof_ival`/`offsetof_ival` `:282-288`,
     `allocate_object`/`load`/`store` `:89-91`, and the pointer/memcpy
     family `:150-225` as their implementations require) add
     `declare {lean} fuel_consumer val …` beside `reader_consumer`.
   - `lean_frontend/CerbFuel.lean:71` `driverFuel : Nat := 100000000` and
     its doc `:53-61`: DELETE; the CLI keeps the only permitted numeral
     (`--fuel N`, default a harness choice) and builds `letI : LemFuel := ⟨n⟩`.
   - `lean_frontend/CerbND.lean`: `:85` `ndDefaultFuel := CerbFuel.driverFuel`
     DELETE; `:150`, `:227`, `:280` (`runND`, `runND1`, `runND1Trace` at
     `ndDefaultFuel`) become `[LemFuel]` entries; `:298-351` hand-written
     `_zero` theorems now DUPLICATE the generated ones (same names,
     `nd_bind_lemFuel_zero`, `liftND_lemFuel_zero`, … `memcmp_load_aux_lemFuel_zero`)
     — delete; `:389-413` `driverFuel_eq`, `*_wrapper_defeq`, `runND_eq`,
     `runND1_eq`: restate as `@f ⟨n⟩ = f_lemFuel n` or delete; `:450`
     hand-written `drive_lemFuel` copy gains `[LemFuel]` (calls
     `driver2_lemFuel fuel …`); `:467` `drive_wrapper_defeq` restated.
   - `lean_frontend/test/Unit/TotalityProofTest.lean:36-87` (52 `rfl`s
     "wrapper = worker at lemDefaultFuel"): restate as
     `∀ n, @f ⟨n⟩ = f_lemFuel n := fun _ => rfl` ("every fuel'd entry is
     fuel-parametric"). `EffectsProofTest.lean:55` (`zeros_aux` at
     `lemDefaultFuel`): same. `FuelExemplar.lean:204-205`
     (`budget_succ`, `lemDefaultFuel_succ`), `:222`, `:238-239`, `:253`,
     `:272`, `:317`: the exemplar becomes the ∀-fuel pattern.
   - `mem.lem` / `ctype.lem:183` / `core.lem:91-92` /
     `defacto_memory_aux.lem:38-39` / `cmm_op.lem:580`: the §9 D2 items.
7. **Restating a consumer hypothesis** (for the cerberus change
   manifest; refined-cerberus carries ~60 sites of the shape
   `potential e ≤ lemDefaultFuel`). Once the fuel is the caller's, the
   hypothesis is against the quantified fuel, not a constant: a statement
   `H e → step_eval_pexpr … e = r` that was proved under
   `potential e ≤ lemDefaultFuel` becomes
   `∀ [LemFuel], potential e ≤ LemFuel.fuel → step_eval_pexpr … e = r`
   (equivalently `∀ n, potential e ≤ n → @step_eval_pexpr ⟨n⟩ … e = r`,
   and for a closed executable `letI : LemFuel := ⟨n⟩`); the shipped-
   constant version is the corollary at `⟨100000000⟩`. The worker-level
   form the exemplar already uses (`f_lemFuel n …` with `n` explicit) is
   unchanged. The two constants (10^8 driver family, 10^6 the rest)
   collapse to ONE hypothesis variable.

## 7. Perf (design note §4.4; report, don't optimize)

Measured, not optimized. Two shapes:

1. **Clean Lean build of the comprehensive corpus** (LemLib + the
   `lean-test` package, `lake build` through `scripts/capped`, 32 cores):
   the BASELINE tree (`git archive 0db35ec`, generated by the baseline
   lem) vs the FINAL tree (`git archive HEAD`, this lem), `.lake` removed,
   sequential, two passes — verbatim:

   ```
   == base (47 sources generated by Lem 0db35ec): clean lake build, LemLib + test package
      exit 0, 8 s wall; Build completed successfully (134 jobs).
   == after (47 sources generated by Lem d80505b-dirty): clean lake build, LemLib + test package
      exit 0, 8 s wall; Build completed successfully (136 jobs).
   --- second pass (repeatability):
   == base (47 sources generated by Lem 0db35ec): clean lake build, LemLib + test package
      exit 0, 8 s wall; Build completed successfully (134 jobs).
   == after (47 sources generated by Lem d80505b-dirty): clean lake build, LemLib + test package
      exit 0, 7 s wall; Build completed successfully (136 jobs).
   ```

   The instance-implicit binder adds no measurable elaboration cost at
   this scale (+2 jobs are the new test modules). At run time the
   instance is one `Nat` argument (a single-field structure is represented
   as its field), the same shape the reader lifting already pays.
2. **The whole suite** (`make lean`, all phases incl. the two-target
   parity runner's 22 probe builds): baseline 3:16 wall (that run stopped
   at the parity phase — the fresh worktree had no `ocaml-lib/_build_zarith`,
   so parity contributed ~0 s); final 6:29.70 wall with the full parity
   leg (`make lean  389.71s user 42.89s system 111% cpu 6:29.70 total`);
   an intermediate incremental run (compile phase only re-touched) was
   1:14. Not comparable phase-for-phase; shape 1 is the controlled
   number. The cerberus-scale measurement (an extra instance argument on
   every fuel'd call in the differential lanes) belongs to the cerberus
   half, on its lanes' wall-clock, as the design note §4.4 says.

## 8. Gates — verbatim

### 8.1 tests/comprehensive `make lean` (final tree, `.tmp/final-comprehensive.log`)

```
=== Generation: 47 passed, 0 failed, 0 skipped ===
Build completed successfully (136 jobs).
=== Panic-path pin (failwithI raise at the L_undefined arm) ===
  OK (leg 1): panic prints the Incomplete Pattern message, then continues with default
  OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1
=== m7 single-evaluation pin (tuple-let RHS runs once) ===
  OK: draws: first=1 second=2
single-evaluation: OK
=== Supply draw-sequence pin (compiled) ===
  OK: compiled draw sequences hold
=== reader_consumer injection pin (compiled) ===
  OK: compiled consumer injection holds
=== Fuel as a quantified parameter (compiled): sufficient fuels agree; exhaustion is loud ===
  OK (leg 1): two sufficient fuels agree; insufficient gives the declared sentinel; callee starts from the full ambient
  OK (leg 2): loud exhaustion at an insufficient runtime fuel fail-stops (exit 134)
=== No fuel numerals in LemLib or generated code (gate) ===
  OK: 219 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F4)
=== Negative probes (must be rejected with the declared error) ===
  [45 × "OK (rejected as declared)" — derived count]
=== Non-Lean invariance ({lean} declares are no-ops for ocaml/hol/isa/coq) ===
  OK: inv_fuel.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_reader_consumer.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_supply.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
=== Two-target parity (OCaml reference vs Lean, compiled) ===
  [7 × "OK: both fail (…); stdout prefix identical", f_int_of_big_num
   "FAIL: failure probe, but the Lean binary SUCCEEDED (exit 0) where the
   OCaml reference fails" + "XFAIL (expected, registered): RULED
   OCaml-target deviation …", 21 × "OK: parity (N lines byte-identical to
   the OCaml reference; pin matches)" incl. p_fuel "(16 lines …)" and
   p_supply_shapes "(34 lines …)", p_str_bytes/p_str_escapes XFAIL (F2,
   pre-existing) — derived counts]
make lean  389.71s user 42.89s system 111% cpu 6:29.70 total
EXIT 0
```

The `p_fuel` leg, from the pin-recording run: `REBASELINED pin …/expected/p_fuel.out`
/ `OK: parity (16 lines byte-identical to the OCaml reference; pin
matches)` — the Lean driver printed `results` at fuels 200 and 100000,
the OCaml driver printed its fuel-free block twice.

### 8.2 lean-lib

`lake build` (capped): `Build completed successfully (37 jobs).`
`#print axioms`: `'LemLibTheorems.PsetJoin.join_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]`, same for `PmapJoin.join_eq`;
the twelve F7 theorems unchanged. `grep -rn "^axiom " lean-lib/
--include="*.lean"`: no hits.

### 8.3 tests/nonlean-regress (final tree)

```
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
```

Boundary re-verification finding (orchestrator, 2026-09-04): the net's
`golden.exitcodes` comparison was locale-fragile — the `for f in *.lem`
glob order follows the environment's collation (`classes`/`classes2`,
`indreln`/`indreln2` swapped elsewhere); the sha manifest was already
`LC_ALL=C sort`ed and unaffected. Fixed at `dfd1a63`: the exit-code rows
are sorted under `LC_ALL=C`; `golden.exitcodes` rebaselined ORDER-ONLY
(`diff <(LC_ALL=C sort <old>) <new>` → exit 0; `golden.sha256`
untouched); re-run, verbatim: `nonlean-regress: OK (893 artifact rows,
216 exit rows, 9 emitters, byte-identical to golden)`.

(One intermediate variant — `fuel_consumer` declared on
`library/relation.lem` — made 37 `lib/tex`, 33 `lib/tex_all`, 1 `lib/lem`,
1 `lib/html`, 1 `lib/ident` rows drift, because the human/echo targets
re-render library source; that variant was withdrawn, §9 D1. No golden
was rebaselined in this arc.)

### 8.4 The gate, plant-tested (`tests/comprehensive/check_no_fuel_numerals.sh`)

Comments are stripped before matching (a HISTORY note may name the
deleted constant; a code token may not). Plants, verbatim:

```
PLANT 1 (F3: a generated worker applied to a literal fuel):
  FAIL (F3): fuel numeral shape found:
…/tests/comprehensive/Test_fuel_param.lean:132: def plant : Nat := spin_lemFuel 5 3
exit=1
PLANT 2 (F2+F4: a global instance in LemLib):
  FAIL (F2): fuel numeral shape found:
…/lean-lib/LemLib.lean:1793: instance : LemFuel := ⟨1000000⟩
  FAIL (F4): fuel numeral shape found:
…/lean-lib/LemLib.lean:1793: instance : LemFuel := ⟨1000000⟩
exit=1
PLANT 3 (F1: a code reference to the deleted default):
  FAIL (F1): fuel numeral shape found:
…/lean-lib/LemLib.lean:1793: def plant2 : Nat := lemDefaultFuel
exit=1
REVERTED:
  OK: 173 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F4)
exit=0
```

(173 files at plant time, before the parity `P_*.lean` modules existed
in the tree; 219 in the final run. Audit M3: the gate ran BEFORE the
parity phase, so a clean run never scanned the `P_*` modules — fixed in
§10: the gate is now the suite's last phase.) Excluded by design: test harnesses
and pins (`LemLibTest.lean`, hand-written `lean-test/Test*.lean`, parity
`Run_*`/`*.main.lean`) — a test suite may choose its fuel.

### 8.5 OCaml byte-identity of the comprehensive corpus

Baseline lem (`0db35ec`) vs this lem, `-ocaml` over every `test_*.lem`,
parity probe and invariance source (`LEMLIB` = this tree's library):
`ml files: base=102 new=103`; `diff -r` of the `.ml` trees:
`Only in .tmp/new-ocaml: inv_fuel.ml` (exit 1 for that one line: the
baseline lem cannot parse the new `fuel_consumer` declare — `inv_fuel.lem
1` vs `0` in the exit lists); every one of the 102 pre-existing `.ml`
files is byte-identical. The cerberus tree: §6.2.

## 9. Decisions for the operator (STOP-and-record items; nothing here was decided by me)

- **D1 — `Pset.tc`: data measure (as landed) or caller-fuelled?** The
  coordinator's brief said "lfp MUST be (a)". `lfpGo` (the primitive) IS
  caller-fuelled; its one caller `tc` passes `(2|r|)^2 + 1`, which I
  classified a data measure (the closure lives in the finite square of
  r's endpoints, so convergence within that many steps is a theorem for
  any total-preorder comparator) — the same form the operator ruled
  admissible for the height indices. The caller-fuelled alternative was
  BUILT: `declare {lean} fuel_consumer val transitiveClosureByCmp` in
  `library/relation.lem`, `set_tcByCmp [LemFuel]`, `tc [LemFuel]`;
  measured consequences: `Lem_Relation.reflexiveTransitiveClosureOn`,
  `withoutTransitiveEdges`, `Lem_Show_extra.stringFromRelation` gained
  `[LemFuel]`; the library assert `withoutTransitiveEdges_3` needed the
  library-assert exemption; 73 human/echo rows of the nonlean-regress
  golden drifted (a library source edit); `p_set_ops` needed a fuel. It
  was withdrawn [AGENT]. If the operator wants (a) for `tc` regardless,
  the withdrawn variant is a 4-line change plus the golden rebaseline.
- **D2 — fuel'd functions as instance methods / in indreln rules**
  (cerberus `Eq ctype`, `Eq core_base_type`, `Eq mem_value`; `monStep`
  rule). Options: (i) cerberus makes those equalities structurally
  recursive (`termination_argument`) — cleanest if Lean's structural
  checker accepts the nested-list recursion; (ii) backend: an instance
  whose methods reach fuel takes `[LemFuel]` (`instance [LemFuel] : Eq0
  ctype`) — mechanically small, but keeping the fail-closed property
  needs type-directed detection of class-method uses at fuel-lifted
  instances (the fixpoint sees `isEqual`, not the instance) — M; (iii)
  hand-written `instance [LemFuel]` via `skip_instances`, same gap. The
  indreln rule cannot take a binder at all: the concurrency model's
  problem to restate. Until decided the backend refuses fail-closed.
- **D3 — `lemLeastFixedPoint`'s silent `| 0 => x`: RESOLVED BY RULE**
  [AGENT applying the USER rule, orchestrator-relayed 2026-09-04]. It is
  lem's own `Set.leastFixedPoint` (set.lem:709-715: `| 0 -> x`), computed
  identically by the OCaml target; the general form exempts values that
  "mirror lem or ISO-C design choices" — a lem design choice, not a magic
  value. Kept as is; the reasoning-artifact audit's remark is withdrawn.
  Other `| 0 =>` arms: every LemLib bounded recursion's is the loud
  `fuelExhaustedWith`; the backend's emitted `| 0 => <sentinel>` is the
  model author's payload — cerberus uses loud/typed payloads at 63 of 64
  declares and one silent VALUE payload (`defacto_memory_aux.lem:469`
  `simplify_integer_value_base` = ``Sum.inr ival_``, "returns its input
  unsimplified", its own comment says), noted for the cerberus half.
- **D4 — `int32FromInteger`-family Overflow raise: FINDING (no code
  change yet, as instructed).** lem's own library semantics
  (`library/num.lem`), verbatim reps: `int32FromInteger` — isabelle
  `((`word_of_int` i) : int32)`, ocaml `Nat_big_num.to_int32`
  (= `BI.int32_of_big_int`, raises on overflow), lean
  `lemInt32OfIntegerExact` (raises); its lem DEFINITION (`:2389-2393`)
  routes through `int32FromNatural`, whose hol rep is `((`n2w` n) :
  int32)` and isabelle `((`word_of_int` (`int` n)):int32)` — both
  MODULAR (`word_of_int`/`n2w` reduce mod 2^32); coq
  `Z.pred (Z.pos (P_of_succ_nat n))` is marked `(* TODO check *)` and
  does not truncate (an acknowledged-incomplete rep, not a specification).
  `int64FromInteger`/`int64FromNatural` (`:2451-2470`) are the same
  shape. `int32FromNumeral`/`int64FromNumeral` (`:828-834`, `:1037-1043`):
  isabelle `word_of_int`, hol `n2w` — modular. Conclusion: lem's
  prover-side meaning of an out-of-range conversion is WRAP; the
  `Overflow` raise is an OCaml-execution artifact of the same kind as X3,
  and under the ruling that the logical semantics is what counts the Lean reps
  (`lemInt32OfIntegerExact`, `lemInt32OfNaturalExact`,
  `lemInt32FromNumeral`, and the `Int64` trio) should become
  `Int32.ofInt`/`Int64.ofInt` (modular), moving parity rows
  `f_int32_overflow` (both-fail → a ruled deviation) and possibly
  `p_int_wrap`. Awaiting the operator's ruling (TODO row 11).
- **D5 — the cerberus half's D2 choice shapes the pin bump**: with (i),
  no backend change; with (ii), one more lem slice before the bump.

## 10. Not done, and why

- Fuel monotonicity is not generated (§5: requires an absorbing typed
  outcome; TODO row 13).
- The remaining WF recursions of LemLib (§4 last row) are left as
  termination-proof form (admissible); converting them is TODO row 12.
- The Ott grammar file carries the new row; derived artifacts not
  regenerated (TODO row 5, pre-existing).
- `.tmp/` (baseline binary, scratch trees, logs) is ephemeral and
  deleted at slice end; everything load-bearing is quoted above.

## 10. Audit response (pre-merge audit `2026-09-04_fuel-parameter-audit-premerge.md` @ `b3d084e`, verdict MERGE-WITH-FIXES, no MAJOR)

One commit on `arc/fuel-parameter`; each item as the auditor asked.

- **M1** (manual asserted a library `fuel_consumer`): the sentence is
  gone; the paragraph now says "The library declares none" and carries
  N1's build-time behaviour.
- **M2** (DESIGN.md contradiction): "No magic values" rewritten ONCE as
  the three admissible forms — (a) caller parameter, (b) termination
  proof, (c) structural recursion on a data measure — quoting the
  operator's aim sentence and general form verbatim; `Pset.tc`'s
  `(2|r|)² + 1` named as a data-DERIVED bound classified (c), D1 pending
  the operator; the draft sentence forbidding data-computed bounds is
  deleted.
- **M3** (gate ran before parity): `lean-no-fuel-numerals` is now the
  suite's LAST phase. Clean run (parity artefacts removed first), the
  gate's line, verbatim:
  `  OK: 219 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)`
  (173 before: the 46 parity `P_*.lean`/`P_*_auxiliary.lean` modules
  were never certified on a fresh tree).
- **M4** (two green evasions): F3 now matches a parenthesised numeral in
  fuel position (`_lemFuel[[:space:]]*\(?[[:space:]]*[1-9]…`); new F5
  matches an anonymous-constructor literal `⟨<numeral>⟩` (`⟨n⟩` with a
  variable stays legal). All eight shapes planted, each red, reverted
  green — verbatim:

  ```
  PLANT A: exit=1 FAIL (F3)                 def plantA : Nat := spin_lemFuel 5 3
  PLANT B: exit=1 FAIL (F2) FAIL (F4) FAIL (F5)   instance : LemFuel := ⟨1000000⟩
  PLANT C: exit=1 FAIL (F1)                 def plantC : Nat := lemDefaultFuel
  PLANT D: exit=1 FAIL (F2)                 instance : LemFuel where fuel := 5
  PLANT E1: exit=1 FAIL (F3)                def plantE1 : Nat := spin_lemFuel (5) 3
  PLANT E2: exit=1 FAIL (F2)                def plantK : Nat := 5 / instance : LemFuel := LemFuel.mk plantK
  PLANT E3: exit=1 FAIL (F4)                def plantInst : LemFuel := LemFuel.mk 5 / attribute [instance] plantInst
  PLANT E4: exit=1 FAIL (F5)                def plantE4 : Nat := @spin ⟨5⟩ 3
    OK: 219 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
  REVERTED exit=0
  ```
- **M5**: `fuel_consumer` added to `test_contextual_keywords.lem` (let-bound
  value, parameter, record field; asserts re-summed to 55).
- **N1**: manual: an undeclared fuel-reading rep fails at the Lean build
  (`failed to synthesize instance of type class LemFuel`) — fail-closed
  at build time, not at generation; cannot be absorbed (no instance exists).
- **N3**: §6 pinned to `de2fbf1bd`; counts recounted (72 declares in 15
  files = 5 numeric + 67 sentinel = 67 wrappers = 67 `_zero` lemmas;
  `LEM_SRC` 86 / `LEM_SRC_LEAN` 85).
- **N4**: X3 addendum cross-reference → §4 table and §9 D4.
- **N6**: TODO row 13 lists both monotonicity routes; the auditor's
  generated completion predicate `f_completes` is the cheaper candidate.
- N2 (cites at Z2), N5 (`heightsOk` preservation is the consumer's slice),
  N7 (`deps/lem-pinned` binary stale — container hygiene, for the
  operator), N8, N9: acknowledged, no change here.

Re-run after the response (this tree), verbatim:

```
=== Generation: 47 passed, 0 failed, 0 skipped ===
Build completed successfully (136 jobs).
  OK (leg 1): panic prints the Incomplete Pattern message, then continues with default
  OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1
single-evaluation: OK
  OK: compiled draw sequences hold
  OK: compiled consumer injection holds
  OK (leg 1): two sufficient fuels agree; insufficient gives the declared sentinel; callee starts from the full ambient
  OK (leg 2): loud exhaustion at an insufficient runtime fuel fail-stops (exit 134)
  [45 × OK (rejected as declared); 3 × invariance byte-identical; parity 21 OK / 7 both-fail / 3 XFAIL — derived]
  OK: 219 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make lean  238.07s user 24.62s system 98% cpu 4:27.39 total
EXIT 0
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
```


## 11. Orchestrator boundary review [AGENT, orchestrator, 2026-09-04]

Two independent re-verifications in this worktree. (1) On `82b14e4`
(before the audit): lem rebuilt from source; `lean-lib` `Build completed
successfully (37 jobs)`; `grep -rn "^axiom " lean-lib/` → 0;
`tests/comprehensive` `make lean` rc 0 with the three registered XFAILs
only; `tests/nonlean-regress/run.sh` FAILED order-only in my locale —
`diff <(sort golden.exitcodes) <(sort .scratch/exitcodes)` IDENTICAL,
sha manifest unchanged — fixed by `dfd1a63` (LC_ALL=C sort, order-only
rebaseline). (2) On `220b31e` (audit response `ca50ffd` + the audit
document `b3d084e` cherry-picked), verbatim:

```
Lem 220b31e
=== Generation: 47 passed, 0 failed, 0 skipped ===
Build completed successfully (136 jobs).
  OK: 219 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
make-lean-rc=0
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
```

(the three `FAIL` lines in the run are the registered XFAILs: the ruled
`f_int_of_big_num` OCaml-target deviation and the two F2 strings rows.)
Pre-merge audit: `2026-09-04_fuel-parameter-audit-premerge.md`
(MERGE-WITH-FIXES, no MAJOR → fixed in `ca50ffd`, §10). Merge ask goes to
the operator on this head, conditional on the consumer's review of the
design note (R1) and the D2/D4 rulings (D4, if ruled "wrap", is one more
commit on this branch before the merge).
