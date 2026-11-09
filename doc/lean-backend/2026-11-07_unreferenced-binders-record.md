# Unreferenced binders and the inert `termination_by` (TODO item 54, lem-lean half): record

Date 2026-11-07. Worker [AGENT], charter
[2026-11-07_worker-charter-unreferenced-binders.md](2026-11-07_worker-charter-unreferenced-binders.md)
(orchestrator [AGENT]; the go-ahead [USER 2026-11-07]). Branch `fix/unreferenced-binders`, base mainline
`mdd/lean-backend` `b154377`; Lean 4.35.0; the cerberus pin (`e6d8db5`) does not move here. Commits: M1
`4a2a72e` (the backend, LemLib, the gate flags), M2 `2d9b36f` (the probes, the measurement), M3 `5362006`
(this record, the docs, the consumer note); then the pre-merge review `b8ba843`
([2026-11-07_unreferenced-binders-premerge-review.md](2026-11-07_unreferenced-binders-premerge-review.md),
verdict not as-is) and its fix round: `c846d39` (the code: review F1 and F3, the probes, the re-gate, the
measurement redone) and the docs commit that carries this text (the dispositions are in the review file).

## 1. Summary

Lean 4.32+ warns `Variable name … is not explicitly referenced` on a pattern variable or parameter bound by
name and unused in its scope (`linter.unusedVariables`), and `unused termination_by, function is not
recursive` on a termination clause attached to a definition Lean's elaborator finds non-recursive. At the
4.35 move the comprehensive suite's `lean-compile` emitted 87 of the first kind and 88 of the second, LemLib's
build 4 of the first; the cerberus generated tree at mainline `1e5f2cbca` replayed 676 and 147 (the charter's
measurement). The backend now (a) binds an unreferenced variable under its source name with a leading
underscore (a name already spelled `_x` is left as it is), decided on the typed AST, in every binding form;
(b) attaches the derived comparison and size
emitters' `termination_by structural` exactly to the definitions that recurse (Lean's own rule, per strongly
connected component, measured); (c) binds the derived `Inhabited` instance's constant-function parameter as
`_`. The suite and LemLib build at zero warnings, and both packages now build with `-DwarningAsError=true`, so
a warning is a build failure from here on. The OCaml output is byte-identical (the suite's invariance lane; the
cerberus OCaml tree regenerated and compared, 86/86 files). The cerberus delta joins the stored warnings one
for one: 601 renames + 75 Inhabited wildcards = the 676 unreferenced-variable warnings, 147 clauses = the 147
inert-clause warnings (§4.2).

## 2. The mechanism (`src/lean_backend.ml`)

### 2.1 Unreferenced binders (`with_binder_scope`, `binder_underscore`; the mechanism comment at `with_binder_scope`)

A binding form renders its patterns under `with_binder_scope scope render`, where `scope` is the list of
expressions in whose scope the patterns' variables are bound: a def clause's body (`funcl_aux`, both the plain
and the fuel'd assembly), an equation clause's body (`render_equation`), a lambda's body (`Fun`), a match arm's
body (`case_line`, `case_line_multi`, and the supply-threaded `Case`), a let's body (`let_body`, now taking
the scope from its one caller; and the supply-threaded `Let_val`), the later lines and the final expression of
a `do` block, the body and the restrictions of a quantifier, and — for a top-level destructuring `let` — the
one bound name each per-name projection references (`with_binder_refs (NameSet.singleton name)`). The
referenced names are the free variables of those expressions (`C.exp_to_free`: substitutions resolved,
shadowing respected) plus the kept names of §3. The set is installed in `St.binder_refs` only around the
pattern rendering (patterns contain no expressions), so no nested form sees an enclosing scope; the pattern
printer's `P_var`, `P_var_annot` and `P_as` cases consult it: a name outside the set renders as `_<name>`
(`binder_underscore`), with the lskip kept in match-arm style. `None` (no scope installed) keeps every name:
the fail-safe direction — a kept name is at most a warning, a wrongly underscored one an unknown identifier at
the Lean build, never a silent change. Not applied while a definition renders as a block comment
(`St.rendering_comment`: dead text keeps the source spelling), to a wildcard, or when the underscored name
would fall into a synthesized binder namespace (§3). The variable's source name is kept under the underscore
deliberately ([AGENT 2026-11-07], the charter's rule): `_err` stays greppable against the lem and the OCaml;
a bare `_` would not. A source name already spelled with the leading underscore — the OCaml convention
cerberus's lem uses for the variables it does not use (`One (_name, setgen) -> …`) — is left as it is: the
first cut prefixed it again (`__name`, 13 cerberus sites and three in the suite; Lean accepts `__name`
silently, which is why no gate caught it), the pre-merge review's F1 found it, and the fix round added the
check and a text pin (`check_unreferenced_binders.py` U2: no identifier in the generated code gains a second
underscore). The kept names of §3 are added only where a clause head's parameters render (`funcl_aux`,
`render_equation`): every text that names them names a parameter, and the first cut's wider set (every
pattern rendered while the definition rendered) left a nested arm or lambda binder spelled like a kept
parameter warning with no remedy but a lem rename (review F3; fixed in the same round, with the two shapes
as probes).

### 2.2 `termination_by` per recursive definition (`lean_block_recursive`)

Probed on 4.35.0 (`lake env lean`, with and without `-DwarningAsError=true`; the files are reproduced in §6):
in a `mutual` block, a clause on a member outside every cycle warns — a non-recursive member (B) AND a member
that only calls into a cycle without being called back (C); a cycle with the clause on one member only is
accepted (D); clauses on exactly the cycle's members and none elsewhere are silent (A). So Lean's rule is per
strongly connected component of the block's call graph, and that is now the emitter's: every def of the
derived comparison block (`t.beq_derived`, `t.compare_derived`, the `*_deriv_aux<k>` helpers) and of the
derived size block (`t.lemSize`, `lemSize_aux<k>`) is produced as (name, text without a clause, callees), and
`lean_block_recursive` (a reachability check from the def's callees back to itself) decides the clause at
assembly. The callees are computed after the text (`leaf_callees`, `build`), so the helpers' on-demand
numbering is unchanged. A list helper always recurses on its tail; an option or sum helper recurses iff its
element type's comparison calls it back — the charter expected the option/sum helpers' clause to be always
inert, but a type with a `maybe t` field puts its option helper in a cycle with `t`'s comparison, and that
helper keeps its clause (the probe type `ot`, §5). The size emitter's former test — "makes a block call" —
was the wrong predicate: a member that only calls into a cycle carried an inert clause (probe C's shape; the
probe member `mC`). The `declare {lean} structural val` path is untouched (user-designated, never inert).

### 2.3 The derived `Inhabited` instance's constant function

`default_value_inhabited` inhabits a function type as `(fun (x<n> : dom) => <inhabitant of rng>)`; the
parameter was a fresh name the body never referenced (the suite's eight remaining errors under the flag, all
this shape: `Test_deriving.lean:444`, `Test_derived_inhabited.lean:260`, …). It is now `(fun (_ : dom) =>
…)`; `generate_fresh_name` and `St.fresh_name_counter`, whose only user it was, are removed.

## 3. The kept-name cases

A binder keeps its spelling whatever the body references when text the backend emits outside the AST names
it. Each is read by `with_binder_scope`:

| Case | Why the name is referenced outside the body | Source |
|---|---|---|
| the designated structural parameter | `termination_by structural <param>` names it | `structural_param` (factored out of `structural_clause`) → `St.keep_binders` around `render_group g`; like every kept name, applied at the clause head only (`with_binder_scope ~params:true`) |
| a `reader_seed` def's seed parameters | injected at every call site inside the body by name, overriding the reader binder | `St.reader_seed_param` (the association's second components) |
| the hoisted `function`-tail binders | the fuel sentinel is applied to them in the worker's `0` arm (`((payload) lemTail)`) | `St.tail_sentinel_args` |
| every identifier of a fuel sentinel's text | the `0` arm is the sentinel text, e.g. `fuelExhausted tag` | `St.fuel_emit`, tokenized by `lean_measure_tokens`, first dotted component |
| a lem variable whose underscored name would start with `_lemReader_`, `_lemSupply` or `_lemIfTail` | the backend synthesizes binders in those namespaces inside bodies (reader parameters, supply binders and values, if-chain continuations); a shadowing binder would redirect their injection sites silently | `binder_underscore` (kept as written: at most a warning) |
| the fuel wrapper's binders, the obligation shell's binders, the `_zero` lemma's binders, `lemHyp`, the measure's parameters | rendered from `binder_of` (the lem names) and applied positionally to the worker, not through the pattern printer | unchanged code (`binder_of`, the wrapper/obligation/`_zero` text) |
| a binder referenced only from text derived from the body (a hoisted let, a `lemLetRhs_` helper, the obligation) | it is a free variable of the body, or passed positionally | the rule is exact; nothing to keep |

The fuel-forms tool (cerberus `lean_frontend/test/Unit/FuelFormsTool.lean`, read only) finds the `lemFuel`
and `lemHyp` binders BY NAME in the generated obligation statement (unchanged text) and compares the worker's
arguments with the wrapper's POSITION BY POSITION, so a worker whose own parameter renders as `_x` is
invisible to it. A designated structural parameter is always referenced (the structural analysis requires a
match on it), so its kept-name path has no observable case and no probe; the reader-seed and hoisted-tail
cases are pinned by the existing `lean-reader-multi` (`seed3 (av := 7) …`) and `lean-fuel-param`
(`lemTail`) checks, the sentinel case by the new probe.

## 4. Measurements (every count derived; the gate lines are in §7)

### 4.1 The suite and LemLib (before: the 4.35 record §4/§7; after: this slice)

| | before | after |
|---|---|---|
| `lean-compile`, `Variable name … is not explicitly referenced` | 87 | 0 (and a build error from now on) |
| `lean-compile`, `unused termination_by, function is not recursive` | 88 | 0 (idem) |
| LemLib build, unreferenced-variable warnings | 4 (`List_extra.lean:39,47`, `Word.lean:197`, `Machine_word.lean:40`) | 0 (idem); `make lean-libs` moved exactly those four lines |

The suite's generated text, base binary (`fddcc4a`) vs the M1 binary, every one of the 148 generated files
compared token-wise (every hunk classified; none unclassified): 88 `termination_by` lines removed (the 88
warnings exactly), 78 binders underscored and 8 Inhabited constant-function binders `x<n>` → `_`. Three of
the 78 were the double underscores of review F1 (`Test_target_reps.lean:55`, `Test_functions.lean:111`,
`Test_misc.lean:91`; no warning behind them), so the honest arithmetic is 75 + 8 = 83 fixes against the 87
warnings of the 4.35 record: four unaccounted for. Not reconciled: the base build's log is not available —
the primary lem-lean checkout's stored traces predate the 4.35 move (2026-09-05, the older message text) and
this slice did not rebuild the base tree to recover it. The gate (the build at zero warnings under the flag)
is the signal that nothing is left; which four warnings the derived count misses is open (§9).

### 4.2 The cerberus expected delta (generation only, no compile; the cerberus re-pin slice verifies it)

The new `lem` run from this worktree (`LEMLIB=<this tree>/library`) over the `frontend/` sources of cerberus
mainline `1e5f2cbca` (extracted from the object store, read-only) with the cerberus Makefile's exact flags
(`-wl ign -wl_rename warn -wl_pat_red err -wl_pat_exh warn -outdir … -cerberus_pp -lean`, the
`LEM_SRC_LEAN` list; then the recipe's `sed '/^import Operators$/d'` on `Core_run.lean`), compared with the
primary checkout's `lean_frontend/generated/` (generated at that commit; `frontend/` clean against it;
`lem`'s warning log identical): 172 files generated, the same set as the reference minus the 57 hand-written
copies; 52 modules differ. The classification is TOKEN-level (a `_` makes a binder one character longer and
the width-100 layout re-wraps: 13 hunks are re-flows at line level by this count, 15 by the reviewer's,
token-identical apart from the shapes below): every hunk is one of three shapes and nothing else moved, and
no identifier gained a second underscore (review F1, re-measured after the fix: 0):

| Module | `termination_by` removed | binders `_name` | Inhabited `x<n>` → `_` |
|---|---|---|---|
| `AilSyntax` | 4 | 0 | 0 |
| `AilTypesAux` | 0 | 15 | 0 |
| `AilTyping` | 0 | 1 | 0 |
| `Annot` | 6 | 3 | 0 |
| `Cabs` | 8 | 0 | 0 |
| `Cabs_to_ail` | 0 | 17 | 0 |
| `Cabs_to_ail_aux` | 0 | 2 | 0 |
| `Cabs_to_ail_effect` | 8 | 9 | 0 |
| `Cmm_aux` | 0 | 1 | 0 |
| `Cmm_csem` | 16 | 120 | 8 |
| `Cmm_op` | 0 | 22 | 0 |
| `Cn` | 10 | 1 | 0 |
| `Constraint` | 4 | 0 | 0 |
| `Core` | 2 | 2 | 0 |
| `Core_aux` | 0 | 23 | 0 |
| `Core_eval` | 0 | 10 | 0 |
| `Core_linking` | 0 | 1 | 0 |
| `Core_reduction` | 8 | 33 | 15 |
| `Core_reduction_aux` | 0 | 1 | 0 |
| `Core_rewrite` | 0 | 3 | 0 |
| `Core_run` | 6 | 41 | 1 |
| `Core_run_aux` | 0 | 2 | 0 |
| `Core_sequentialise` | 0 | 3 | 0 |
| `Core_typing` | 0 | 53 | 0 |
| `Core_typing_aux` | 0 | 5 | 0 |
| `Ctype` | 0 | 1 | 0 |
| `Ctype_aux` | 2 | 3 | 0 |
| `Defacto_memory` | 0 | 92 | 0 |
| `Defacto_memory_aux` | 0 | 20 | 0 |
| `Defacto_memory_types` | 2 | 0 | 0 |
| `Desugaring_init` | 6 | 1 | 6 |
| `Dlist` | 2 | 0 | 1 |
| `Driver` | 2 | 17 | 0 |
| `ErrorMonad` | 2 | 0 | 1 |
| `Errors` | 14 | 0 | 0 |
| `Formatted` | 4 | 5 | 0 |
| `GenTypesAux` | 0 | 1 | 0 |
| `GenTyping` | 2 | 45 | 0 |
| `Implementation` | 0 | 1 | 0 |
| `IntegerImpl` | 2 | 4 | 2 |
| `IntegerType` | 4 | 0 | 0 |
| `Mem` | 0 | 2 | 0 |
| `Mem_common` | 14 | 1 | 0 |
| `Mini_pipeline` | 0 | 2 | 0 |
| `Monadic_parsing` | 2 | 0 | 1 |
| `Nondeterminism` | 5 | 9 | 1 |
| `Scope_table` | 0 | 1 | 0 |
| `Symbol` | 4 | 1 | 0 |
| `Translation` | 2 | 24 | 0 |
| `Translation_aux` | 2 | 3 | 39 |
| `TypingError` | 2 | 0 | 0 |
| `Undefined` | 2 | 0 | 0 |
| **total (52 modules)** | **147** (29 modules) | **601** (41 modules) | **75** (10 modules) |

The join against the warnings Lake stored for the primary checkout's last build (`lean_frontend/.lake/build/
lib/lean/<Module>.trace`, read only; the message `generated/<Module>.lean:<line>:<col>: Variable name `<x>`
is not explicitly referenced`): 676 unreferenced-variable warnings in 44 generated modules, every one
matched by module, line and name by a rename (601) or an Inhabited wildcard (75), and no rename or wildcard
without a warning — 601 + 75 = 676 exactly; 147 inert-clause warnings in 29 modules, equal per module to the
clauses removed. The two further stored warnings are outside the generated set (`Core_unstruct`, 4, not in
the Lean build; `CerbMem.lean`, 2, hand-written: the half-mirrors slice's). The first cut's 614 = 601 + 13
double underscores (review F1). No hand-written cerberus Lean (171 files under `lean_frontend/`,
`test/Unit/`, `speclab/`, read only) passes a named argument to a parameter of a generated definition that
the rule underscored (0 sites), so the delta is text-only for the consumer.

The OCaml tree (`-ocaml` over `LEM_SRC`, then the recipe's four `sed`s) against the primary's
`ocaml_frontend/generated/`: 86 files compared, 0 differ (byte-identical), before and after the fix.

## 5. The probes (M2; `tests/comprehensive/test_unreferenced_binders.lem`, 16 asserts)

Derived instances: `nonrec_t` (a non-recursive variant with a nullary constructor after a block one, so it
takes the derivation rather than `deriving`: no clause on `beq_derived`/`compare_derived`, no `lemSize`),
`rec_t` (clause on both and on `lemSize`), the block `mA`/`mB`/`mC` (`mA` recursive: clauses; `mB` outside
every cycle and `mC` calling into `mA` without being called back: none, on the comparisons and the sizes),
`ot` (an option field: the option helpers in the cycle keep their clause). Binding forms: def parameters,
lambda, match arm, `function` arm, a nested tuple pattern, a let pattern, a named pattern (`y@((_x, w))`), a
local lambda, shadowing (`fun (_x : Nat) => let x := 5; x`), a `partial def`'s parameter, equation clauses,
an instance method (`tag_of _x := 42`), a do line (`let (_x : Nat) ←`), the per-name projections of a
top-level destructuring let (`let (ta, _tb) := …; ta` / `let (_ta, tb) := …; tb`), and a kept name: a
fuel'd def whose sentinel text names `tag`, unreferenced in the body (`def loop_lemFuel (lemFuel : Nat) (tag
: Nat) (n : Nat)`). From the review's fix round: a source name already spelled `_x`, unreferenced (`def
keep_us (_x : Nat) (y : Nat)`) and referenced (`def use_us (_x : Nat) : Nat := _x + 1`), and in an arm
(`arm_us`: `| some _v => 0`); the kept names protecting the clause head only — a fuel'd def whose sentinel
names `tag` with a nested arm binder `tag` (`def loop_arm_lemFuel (lemFuel : Nat) (tag : Nat) (o : Option
Nat)`, its arm `| some _tag =>`) and a structural def `slen` on `l` with a nested lambda binder `l` (`(fun
(_l : List Nat) => 1)`, `termination_by structural l`). Pins: the Makefile target `lean-unreferenced-binders` — leg 1 `check_unreferenced_binders.py`
over the generated module (U1 the exact binder lines, U2 no double-underscore identifier in the code, T1
the clause present on exactly the recursive definitions and absent on the others, V vacuity; plants P1–P3 in its header, run on a scratch copy: P1 `(_y :
Nat)` edited back → `FAIL (U1) … lacks the line`, P2 the clause under `rec_t.beq_derived` deleted → `FAIL
(T1): rec_t.beq_derived recurses but carries no termination_by clause`, P3 a clause added under
`nonrec_t.beq_derived` → `FAIL (T1): nonrec_t.beq_derived does not recurse but carries a termination_by
clause`; a fourth plant, `__v` edited into an arm, fails U1 and U2); leg 2, generation only, a lem def with parameters `lemReader_x`, `lemSupply_y`, `lemIfTail_z`,
`plain`, all unreferenced: the three keep their names, `plain` is `_plain`; leg 3 the negative plant
`lean-test/TestWarningPlant.lean` (a `lean_lib WarningPlant`, not a default target) must FAIL under the
package's `-DwarningAsError=true` with both kinds as `error:`. The hand-written
`lean-test/TestUnreferencedBindersCheck.lean` pins the rendered binder NAMES through Lean's named-argument
syntax (`def_params (x := 1) (_y := 2)`, `loop_lemFuel (lemFuel := 3) (tag := 9) (n := 2)`, `keep_us (_x :=
1) (y := 2)`, `use_us (_x := 1)`, `loop_arm_lemFuel (lemFuel := 2) (tag := 9) (o := some 4)`) and the values
by `rfl`/`decide` through the derived comparisons and sizes with and without a clause. The suite's
`lean-multiclause` pin follows the underscored binder (`| (_x :: xs) => 1 + len2 xs`). No parity probe was
added: the OCaml side of every probe shape is unchanged by construction (the emitter is untouched) and the
suite's invariance lane and the cerberus byte-compare cover it.

## 6. The Lean 4.35.0 probes behind §2.2 (scratch, `lake env lean` under the cap)

A (`a_cycle_only.lean`): `mutual def ra … termination_by structural x; def rb … termination_by structural x;
def nr (x : Nat) : Nat := match x with | 0 => 1 | n+1 => n end` — exit 0, no output, with and without
`-DwarningAsError=true`. B: the clause added under `nr` — `warning: unused `termination_by`, function is not
recursive` (8:0); with the flag `error:` and exit 1. C: `def cc (x) := match x with | 0 => 1 | n+1 => ra n`
with a clause — the same warning at 8:0. D: the cycle `ra`/`rb` with the clause on `ra` only — exit 0, no
output. E: `def f1 (x y : Nat) := x`, `some v => 0`, `(a, b) => a` warn on `y`, `v`, `b` with the hint
`prefix the name with _`; the `_y`/`_v`/`_b` twins do not; under the flag the three are errors, exit 1.

## 7. Gates (verbatim last lines)

### 7.1 M1 (commit `4a2a72e`)

Root `make` (`scripts/ce make`; exit 0): no warning in `src/lean_backend.ml` (the upstream files' 20
warnings as before). LemLib from `lean-lib/`, `CERB_MEM_MAX=32G capped lake build` after `make lean-libs`
(exit 0; `warning:` lines 0):

    info: LemLibTheorems.lean:553:0: 'LemLibTheorems.BeqLattice.isEqual_unit' does not depend on any axioms
    ✔ [37/39] Built LemLib.Machine_word (752ms)
    ✔ [38/39] Built LemLib.Pervasives_extra (167ms)
    Build completed successfully (39 jobs).

`make -C tests/comprehensive lean CAPPED=…/cerberus-lean/scripts/capped CERB_MEM_MAX=32G` through
`scripts/ce` (exit 0; `warning:` lines in the whole log 0; the 24 `FAIL` substrings are the parity lane's 11
registered XFAIL reports and the expected OCaml-side failures of its failure probes):

    === Generation: 74 passed, 0 failed, 0 skipped ===
      OK: Test_comments.lean: comments preserved, layout sound
      OK: Test_layout.lean: layout sound (15 alternatives, 2 lets, 14 comments, width 100)
      OK: Test_text_fidelity.lean Test_text_fidelity_auxiliary.lean: target_rep text intact
      OK: equation form for f and len2, match form for g
    Build completed successfully (213 jobs).
    parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
      OK: 12 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
      OK: 535 Lean files scanned; no instance of the 5 instance-reader classes (NegImpl.Sw, NegImpl.Sw2, Sw, TestInstanceReaderImpl.Md, TestInstanceReaderImpl.Sw)
      OK: 328 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
    make lean exit=0

(134 negative probes "OK (rejected as declared)", 11 invariance witnesses "OK: inv_… byte-identical across
ocaml/hol/isa/coq".) Two earlier runs of the same suite on the branch were red and are the plants of the
gate flag: the first at `lean-multiclause` (the pin `(x :: xs)` against the new `(_x :: xs)`), the second at
`lean-compile` with exactly eight `error: … Variable name `x<n>` is not explicitly referenced` — the
Inhabited constant-function binders of §2.3, which the flag turned from warnings into the build failure
that found them.

### 7.2 M2 (commit `2d9b36f`)

`make -C tests/comprehensive lean CAPPED=…/cerberus-lean/scripts/capped CERB_MEM_MAX=32G` through
`scripts/ce` on the M2 tree (exit 0; `warning:` lines in the whole log 0; the 11 `FAIL` substrings of the
parity lane are its registered XFAIL reports):

    === Generation: 75 passed, 0 failed, 0 skipped ===
      OK: Test_comments.lean: comments preserved, layout sound
      OK: Test_layout.lean: layout sound (15 alternatives, 2 lets, 14 comments, width 100)
      OK: Test_text_fidelity.lean Test_text_fidelity_auxiliary.lean: target_rep text intact
      OK: equation form for f and len2, match form for g
    Build completed successfully (216 jobs).
    === Unreferenced binders and the per-definition termination_by (TODO item 54) ===
      OK: 18 binder lines as pinned; termination_by on 12 of 46 definitions, exactly the 12 that recurse; none on the 8 that do not
      OK (keep-guard leg): names in the synthesized binder namespaces are kept; a plain unreferenced one is underscored
      OK (plant): both warning kinds are build errors under -DwarningAsError=true (lake exit 1)
    parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
      OK: 12 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
      OK: 541 Lean files scanned; no instance of the 5 instance-reader classes (NegImpl.Sw, NegImpl.Sw2, Sw, TestInstanceReaderImpl.Md, TestInstanceReaderImpl.Sw)
      OK: 331 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
    make lean exit=0

(134 negative probes "OK (rejected as declared)", 11 invariance witnesses OK.) The target's first standalone
run was red on the plant leg's own check — `FAIL (plant): no unreferenced-variable error:` followed by
`error: TestWarningPlant.lean:8:33: Variable name `y` is not explicitly referenced.` — the expected message
carries the file location the pattern lacked; the plant build itself failed as required both times. The
check script's plants (P1–P3) were run once on a scratch copy of the generated module; each fails with the
message quoted in §5, the unplanted control passes.

### 7.3 The review's fix round (commit `c846d39`)

Root `make` after the two `src/lean_backend.ml` edits (`scripts/ce make build-lem`, exit 0; no warning in
`src/lean_backend.ml`). `make lean-libs` with the fixed binary: `git status --short lean-lib` empty (no library
name is spelled `_x`). LemLib from `lean-lib/`, `CERB_MEM_MAX=32G capped lake build` (exit 0; `warning:` lines
0):

    info: LemLibPmapLaws.lean:559:0: 'Pmap.cmpLaws_defaultCompare_string' depends on axioms: [propext, Classical.choice, Quot.sound]
    Build completed successfully (39 jobs).

`make -C tests/comprehensive lean CAPPED=…/cerberus-lean/scripts/capped CERB_MEM_MAX=32G` through
`scripts/ce` (exit 0; `warning:` lines in the whole log 0; the parity lane's 11 `FAIL` substrings are its
registered XFAIL reports):

    === Generation: 75 passed, 0 failed, 0 skipped ===
      OK: Test_comments.lean: comments preserved, layout sound
      OK: Test_layout.lean: layout sound (15 alternatives, 2 lets, 14 comments, width 100)
      OK: Test_text_fidelity.lean Test_text_fidelity_auxiliary.lean: target_rep text intact
      OK: equation form for f and len2, match form for g
    Build completed successfully (216 jobs).
    === Unreferenced binders and the per-definition termination_by (TODO item 54) ===
      OK: 25 binder lines as pinned, no double underscore; termination_by on exactly the 12 derived definitions that recurse (plus 1 structural declare) of 52; none on the 8 derived ones that do not
      OK (keep-guard leg): names in the synthesized binder namespaces are kept; a plain unreferenced one is underscored
      OK (plant): both warning kinds are build errors under -DwarningAsError=true (lake exit 1)
    parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
      OK: 12 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
      OK: 541 Lean files scanned; no instance of the 5 instance-reader classes (NegImpl.Sw, NegImpl.Sw2, Sw, TestInstanceReaderImpl.Md, TestInstanceReaderImpl.Sw)
      OK: 331 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
    make lean exit=0

(134 negative probes "OK (rejected as declared)", 11 invariance witnesses OK.) The checker's control on the
regenerated probe and its plants P1–P4 (P4: a `__v` edited into an arm → `FAIL (U1) … lacks the line:   | some
_v => 0` and `FAIL (U2): … has a double-underscore identifier: line 446: | some __v => 0`). The cerberus
measurement of §4.2 was redone with this binary (`lean gen exit=0`, `ocaml gen exit=0`, `ocaml compared 86
differing 0`, `lean lem.log identical`).

## 8. What the cerberus half does

The re-pin recipe and the expected delta are in the consumer note
[2026-11-07_consumer-note-cerberus-unreferenced-binders.md](2026-11-07_consumer-note-cerberus-unreferenced-binders.md).

## 9. Open findings

1. (Resolved by the review's fix round.) The first cut's cerberus excess over the logged warnings — 689
   against 676 — was the 13 double underscores of review F1; after the fix the join is exact (§4.2). The
   suite's count stands at 75 + 8 = 83 fixes against the 87 warnings of the 4.35 record, four unaccounted
   for and not reconciled (§4.1: the base build's log is unavailable; the gate is the signal).
2. The `_lemReader_`/`_lemSupply`/`_lemIfTail` guard leaves a warning standing for a lem variable spelled
   like a synthesized binder and unreferenced; the suite's generation-only leg pins the behaviour, no
   compiled probe exists (it would warn). No such variable is in the suite or in cerberus (the delta has no
   kept name of that shape). The kept-name over-approximation the review's F3 found (a nested binder spelled
   like a kept parameter) is closed by the narrowing of §2.1, so this guard is the one remaining shape.
3. The 4.35 record's `tests/backends` measurement (52 warnings of the first kind) is not re-measured: that
   target is red before its build (TODO item 56).
4. `lake check` (the kernel replay of LemLib's closure) was not re-run: no proof changed; the LemLib text
   moved four binder names and `LemLibTheorems` built unchanged. The operator's `lake check` outside the
   sandbox remains the gate at the re-pin claim point, as at the 4.35 move.
5. The `-DwarningAsError=true` flag is on two of the repository's five lakefiles — `lean-lib/lakefile.lean`
   and `tests/comprehensive/lean-test/lakefile.lean`, the two the gates build. The other three are outside
   the rule: `tests/backends/lean-test` is red before its build (TODO item 56), `examples/cpp` and
   `examples/ppcmem-model` are historical examples outside every gate (README, "Validation levels"); none
   is a claim surface (review F5).

## 10. Files

M1: `src/lean_backend.ml` (`St.binder_refs`, `St.keep_binders`; `lean_block_recursive`; `with_binder_refs`,
`with_binder_scope`, `binder_underscore`, `binder_name_output`; the binding-form sites; `structural_param`;
the derived comparison and size emitters; `default_value_inhabited`; `generate_fresh_name` removed),
`lean-lib/lakefile.lean` and `tests/comprehensive/lean-test/lakefile.lean` (`-DwarningAsError=true`),
`lean-lib/LemLib/{List_extra,Word,Machine_word}.lean` (regenerated), `tests/comprehensive/Makefile` (the
multiclause pin). M2: `tests/comprehensive/test_unreferenced_binders.lem`,
`tests/comprehensive/check_unreferenced_binders.py`, `tests/comprehensive/lean-test/TestUnreferencedBindersCheck.lean`,
`tests/comprehensive/lean-test/TestWarningPlant.lean`, the Makefile target `lean-unreferenced-binders`
and the lakefile roots/`WarningPlant` lib. M3: this record, `TODO.md` (54 closed), `DESIGN.md`,
`../manual/backend_lean.md`, `README.md` (the warning rule), `RECORDS.md`, the consumer note.

## 11. Provenance

[USER 2026-11-07] the go-ahead for the item (the charter's provenance); the working-practices rule that
warnings are fixed, never suppressed. [AGENT 2026-11-07]: the per-SCC rule for the clause (Lean's, measured)
in place of the charter's per-kind expectation; `_<name>` rather than `_` for user binders and `_` for the
Inhabited constant function's synthesized one; the `-DwarningAsError=true` flag on both packages as the gate
(the charter's proposal; the operator may strike it); the three synthesized-namespace prefixes as the only
names the rule leaves alone. The review's fix round [AGENT 2026-11-07]: a source name already spelled `_x`
is left as it is (F1); the kept names narrowed to the clause head rather than recorded as a hole (F3: the
hole had no remedy under the flag but a lem rename, the narrowing is three call sites and closes it); the
suite's four-warning gap stated rather than rebuilt (F4: a base rebuild for a P3 count on a shared box).
