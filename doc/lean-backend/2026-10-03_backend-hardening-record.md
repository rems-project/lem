# Backend hardening: package A (correctness and fail-closed) and package C (cleanup) (2026-10-03)

Branch `arc/backend-hardening` from mainline `mdd/lean-backend` at
`5dfcd25`. This record covers package A of the arc that acts on two
reports of 2026-10-03 against `5dfcd25`: the read-the-code review of the
backend and LemLib (the "code review": items H1, H2, M1, M2, W8, TODO 37)
and the behavioural noodler (the "noodle report": findings 1–6). Package C
(cleanup, no output change) is a later slice; package D is out of scope.

## Rulings (operator, 2026-10-03, paraphrased)

- Packages: A (correctness + fail-closed) and C (cleanup, no output
  change), both the recommended options. C is a later slice; D is not in scope.
- #1 min/max: register as a deviation.
- #2 the BEq bridge: design pass first. Another agent handles it; LemLib's
  instance priorities are not changed here.

Every decision below that is not one of these is [AGENT].

## Method

Each item was reproduced first on `5dfcd25` (the worktree before any
change), then fixed, then given a `tests/comprehensive` test that fails on
the before-fix binary and passes after (§"Plants"). The before-fix binary
is a scratch build of `git archive 5dfcd25`. Lean is 4.32.2; every Lean
invocation ran through `cerberus-lean/scripts/capped`. The consumer inputs
were frozen: Cerberus at `51a7402ce`, linksem at `f54d119`.

## Items

### 1. (#4) The Lean annotation words as `target_rep` parameter names — FIXED

- Reproducer: ``declare ocaml target_rep function foo fuel = `Stdlib.succ` fuel``
  → `File "pk.lem", line 4, character 38: Syntax error`; the same line with
  `x` is accepted; upstream Lem accepts `fuel`.
- Cause: `src/parser.mly` `x_ls : | X x_ls` consumed the raw `X` token, while
  the lexer tokenizes the thirteen annotation words for every target; only
  the `x` nonterminal turned them back into identifiers.
- Fix (shared code): a nonterminal `x_tok` (the `X` token or any of the
  thirteen word tokens, yielding the same `(skips, text)` pair) used by both
  `x` and `x_ls`; `loc ()` spans are unchanged. `ocamlyacc -v`: 2
  shift/reduce, 2 reduce/reduce, 5 rules never reduced — identical to the
  fork before the change and to upstream.
- Non-Lean output: `make nonlean-regress` byte-identical; the drift check
  below. The change accepts programs the fork rejected; it rejects nothing
  it accepted.
- Test: `test_contextual_keywords.lem` — an OCaml `target_rep` with
  parameter `fuel` and a Lean one with parameters `reader supply`, both
  applied and asserted.

### 2. (#5) Record fields named like Lean keywords or structure-generated names — FIXED (escape) / REFUSED (generated names)

- Reproducer: `type r = <| at : nat; other : nat |>` → `structure r where\n  at : Nat`
  (Lean: `unexpected token 'at'`), while the literal `{ «at» := default, … }`
  was escaped; `mk : nat` → `Invalid field name mk: This is the name of the
  structure constructor`; `casesOn` → `(kernel) constant has already been
  declared 'r.casesOn'`.
- Measured (plain Lean 4.32.2, a structure, a recursive structure and the
  single-constructor inductive with accessors — the three shapes the
  backend emits): `mk rec recOn casesOn noConfusion noConfusionType` fail in
  all three; `below brecOn` fail for the recursive structure only;
  `binductionOn ibelow induct sizeOf injEq inj toString default ext ext_iff
  mk_inj sizeOf_spec` are fine.
- Decision [AGENT]: keywords are ESCAPED at every site, so a field keeps
  its name (DESIGN: fields keep their Lem names); the eight generated names
  are REFUSED at generation, naming the field and the Lean declaration —
  escaping cannot help («rec» is rec), the reserved-name pass does not
  rename fields (DESIGN "Reserved-name avoidance"), and a rename would be a
  consumer-visible API change applied across six emission sites.
  `below`/`brecOn` are refused for every record (TODO item 47 notes the
  over-refusal for non-recursive ones).
- Fix: `field_ident_to_output` (projection, literal, update, field update)
  escapes; the new `field_decl_output` is the declaration side at the
  three sites (structure field, mutual-structure field, indexed
  single-constructor field); the accessor defs of a mutual record and the
  positional update escape too; `lean_check_type_block` refuses the
  generated names.
- Tests: `test_records.lem` (thirteen keyword fields: projection, literal,
  update, pattern, equality), `test_mutual_record_order.lem` (keyword
  fields of a mutual record, through the accessors),
  `negative/neg_record_field_mk.lem`, `neg_record_field_casesOn.lem`
  (the inductive form).
- Consumers: neither Cerberus nor linksem has a field in either class
  (grep of the frozen sources); their trees are byte-identical.

### 3. (#6) A type variable named like a type or value in scope — FIXED (values) / REFUSED (type definitions)

- Reproducer: `type t = A | B` with `let f (x : 't) (y : t) : nat = tn y`
  → `def f { t : Type } (x : t) (y : t)` (`y` has type `t` but is expected
  to have type `_root_.t`); `let a : nat = 3` with `let f (x : 'a) : nat = a`
  → `a` has type `Type`.
- Fix: `lean_tyvar_renames_for` collects every name the definition refers
  to — the Lean name of each constant (`exp_constants`), the Lean name and
  the components of a Lean target representation of each type constructor
  in the type of any sub-expression or pattern (`lean_types_of_exp`,
  `lean_types_of_pat`, `lean_type_path_names`) — and a type variable equal
  to one of them is rendered under a fresh PRIMED name (`t'`, `t''`, …) that
  is none of those names, none of the other type variables, none of the
  definition's binders (`exp_bound_names`, `pat_to_bound_names`) and not
  reserved. The map is [render]-scoped (`St.tyvar_renames`, set in
  `val_def`, restored by `Fun.protect`) and consulted by the implicit
  binders, both source-type renderers, the class-constraint binders and the
  comparison-dictionary binders.
  - Why primed: a digit-suffixed candidate met Lem's own renamer, which
    turns a colliding LOCAL binder into `t1` at render time, after the map
    is computed (first attempt: `let t = tn y` became `t1` and so did the
    type variable; the Lean error was `List t1` applied to a `Nat`). Lem's
    renamer (`default_avoid_f`, `Name.fresh`) never produces a prime.
  - Type DEFINITIONS are refused, not renamed [AGENT]: a type parameter's
    name is part of the generated API (`inductive t (a : Type)`, named
    arguments), and the collision is a rare source condition; numeric type
    variables are not renamed (no collision shape known). TODO item 47.
- Tests: `test_tyvar_collision.lem` (type and value collisions, a binder
  named like the first candidate, a nested annotation plus a local named
  like the type), `negative/neg_tyvar_type_param_collision.lem`.
- Consumers: byte-identical trees, so no definition of either mentions a
  name equal to one of its type variables.

### 4. (#8) Mutual-record update does not parenthesise or bind its base — FIXED

- Reproducer (heterogeneous block, `skip_instances`): `<| mkr n with f = 5 |>`
  → `(r.mk 5 (mkr n.g))`, which Lean reads as `mkr (n.g)`; a conditional
  base likewise; and the base was re-rendered per unchanged field.
- Fix: `(let lemRecBase := mkr n; r.mk 5 lemRecBase.g)` — the base is
  bound once. `lemRecBase` joins `lean_reserved_exact_names`; a free
  variable of that name in the base or an updated value, or a constant
  rendering to it (`lean_reserved_capture_check`), is refused.
- Tests: `test_mutual_record_order.lem` (an application base, a
  conditional base), `negative/neg_recup_reserved_base.lem`.

### 5. (#9) Generation exponential in wide wildcard patterns — FIXED

- Reproducer (`lem -lean`, a constructor pattern of N−1 wildcards): N=45
  1.6 s, N=47 >120 s, N=50 >120 s; `-ocaml`, `-coq`, `-hol`, `-isa` on N=47:
  1.4–1.7 s. So the cost was in the Lean pipeline after pattern compilation
  (the Coq pipeline shares `is_coq_exp`/`check_match_exp`).
- Cause (stack sample via a temporary `Sys.catch_break` and `-debug`):
  `Lean_layout.be`/`fits` nested dozens deep. The Wadler/Leijen printer's
  `be` decided a Break-mode group by `fits` over a `Seq.t` candidate, then
  re-ran the same `be` to emit it; OCaml's `Seq` is call-by-name, so every
  consumer recomputed the candidate's tail, and each recomputation
  re-decided every Break-mode group that followed on the line — exponential
  in the number of sibling groups on a line that overflows the width. The
  cliff at 46→47 is where `| C _ _ … z =>` stops fitting in 100 columns.
- Fix (`src/lean_layout.ml`): `Seq.memoize` on the candidate of `Group` and
  `Union` — the call-by-need sharing Wadler's complexity argument assumes.
  The decisions are the same, so the output is unchanged (consumer trees
  byte-identical). After: N=47/50/55 1.7 s, N=150 1.6 s, the noodler's
  `t_tuple60` 1.6 s, `t_ctor60_vars` 1.4 s (was 17.6 s).
- Test: `test_wide_patterns.lem` (a 120-field constructor — under the item 6
  limit — with first/last patterns, 60-tuples), compiled and asserted; the
  suite phase `lean-wide-patterns` generates it under `timeout 60` first in
  the suite (`LEAN_WIDE_PATTERNS_SECONDS`), so a regression fails loudly
  instead of hanging the later phases.

### 6. (#3) Records with 128 or more fields segfault at run time — REFUSED at generation

- Confirmed in plain Lean 4.32.2 (no LemLib), binaries run with arguments
  so nothing folds: a 128-field structure of `Nat` exits 139, 127 prints;
  a 128-argument constructor exits 139; 127 `Nat` fields plus one `Bool`
  (1025 bytes) exits 139; 128 and 200 `Bool` fields (one byte each) print.
  So the limit is the object size: header plus pointer-sized fields past
  the runtime allocator's 1024-byte small-object limit. No sound workaround
  that keeps the record's semantics exists at the backend level.
- Fix: `lean_check_constructor_width` refuses a record or constructor with
  more than `lean_max_constructor_fields = 127` fields, counting every field
  at the pointer size (the upper bound), with a message naming the count,
  the limit, the crash and the remedy. Conservative by construction: it
  admits exactly the widths that cannot reach the limit and over-refuses a
  wide record of one-byte fields, loudly. The check runs from `def`'s
  `Type_def` arm (`lean_check_type_block`) so single records, which `def`
  dispatches straight to `type_def_record`, are covered (the first version
  sat in `type_def` and missed them; caught by the reproducer).
- Not a magic value: it mirrors a limit of the Lean runtime, not a choice
  about the semantics; the OCaml target is untouched.
- Tests: `negative/neg_record_width_128.lem`, `neg_variant_width_128.lem`;
  the 120-field constructor of `test_wide_patterns.lem` is the positive
  side.

### 7. (#7) `termination_argument … = automatic` on an `n - 1` recursion — NOT FIXED; DESIGN corrected

- Reproducer: `let rec cnt n = if n = 0 then 0 else 1 + cnt (n - 1)` with
  the declare → `def cnt (n : Nat) : Nat := lem_if n == 0 then 0 else 1 + cnt (n - 1)`
  → `fail to show termination … h✝ : ¬(n == 0) = true ⊢ n - 1 < n`.
- Measured, plain Lean 4.32.2: `if n = 0` (Prop) passes; `if (n == 0) = true`
  with core's `BEq` fails by default and passes with
  `decreasing_by all_goals simp_all; omega` (also `if h : …` + `simp at h;
  omega`). With LemLib imported the condition is
  `@BEq.beq Nat (@Lem_Basic_classes.instBEqOfEq0 Nat Lem_Num.instEq0Nat_1) n 0`
  (`#synth BEq Nat` → the bridge), and `simp_all`, `simp at h` and `omega`
  all fail: "No usable constraints found".
- Decision [AGENT]: no clean general fix exists on this side of the `BEq`
  bridge design pass (#2, "Design pass first", another agent). A
  `decreasing_by` script would have to unfold the bridge's instance chain
  per base type — a special path for one shape, tied to an instance design
  under revision. A generation-time refusal is not possible either (the
  backend cannot know which recursions Lean's checker will accept) and would
  break the consumers: Cerberus declares `automatic` on four structural
  list recursions (`utils.lem`), linksem on `unzip3`. The failure is a loud
  Lean build error, so nothing is silent. DESIGN's row and the manual no
  longer promise "total either way"; they state the limit, the measured
  cause and the remedy (`fuel`/`fuel_measure`/`structural`). TODO item 45
  carries the fix, sequenced after the bridge pass.

### 8. Fail-open spots from the code review — FIXED

- `type_def_indexed` `| _ ->` emitted an empty `inductive … Type 1 where`:
  now raises (`Te_abbrev` reaching it is an internal error, as in `tyexp`;
  `Te_opaque` was already matched earlier).
- `P_num_add` rendered `(name + k)` "invalid Lean but visible": now raises
  unless `St.rendering_comment` (library text behind a representation).
- `lean_cmp_prepass` `depth > 50 → default_all ()` silently
  over-approximated comparison binders (which changes a declaration's
  type): now the same loud refusal as its twin in
  `lean_tuple_inst_demands`.
- The W8 non-exhaustive match in the derived-size builder (`CSfn`
  missing): `CSbad | CSfn` now raise an internal error (`lean_size_shape`
  produces neither); the fork's only default-flag warning in
  `lean_backend.ml` is gone.
- `process_file.ml` ignored `Sys.command "mkdir -p"`: replaced by
  `Sys.mkdir` with parents, a failure a fatal error naming the directory.
  Test: suite phase `lean-outdir-refusal` (`-outdir Makefile/sub`, whose
  parent is a file). TODO item 37 closed.
- No test reaches the three internal-error raises (the inputs do not exist
  after pattern compilation / type-def dispatch / the size shape
  analysis); they are recorded here.

### 9. State fixes — DONE

- `lean_cmp_bounds` moved into `St` ([invocation] lifetime, like
  `reader_lifted`), reset by `reset_invocation`; `if_tail_counter`
  ([invocation]) and `current_type_block` ([file]) reset too, and the new
  `tyvar_renames` ([render]).
- `lean_analysis_prepass_all` now runs `lean_cmp_prepass`, in the order
  `lean_defs` uses, so a module typechecked but not emitted in an
  invocation contributes its comparison-binder demands.
- `reset_invocation` still has no caller (TODO item 6 is the threading
  work); unchanged.

### 10. (#1) `min`/`max` under a user `Ord` instance — REGISTERED as a ruled deviation

- Reproducer (noodle `p_user_ord_instance`): `min (T 1 0) (T 2 0)` is
  `(1, 0)` on OCaml and `(2, 0)` on Lean; everything else about the
  instance agrees.
- Cause: `library/basic_classes.lem` `defaultMax = maxByLessEqual (<=)`
  with ``declare ocaml target_rep function defaultMax = `max` `` (Stdlib's
  structural `max`); upstream report `doc/upstream-tray/11-default-max-min-structural-on-ocaml.md`.
- Ruling: [USER 2026-10-03] register it as a deviation. No OCaml
  representation is changed.
- Register: `parity/probes/p_user_ord_minmax.lem` (the instance's `<=`,
  `min`/`max` both ways, and the explicit `maxByLessEqual (<=)` /
  `minByLessEqual (<=)` lines that agree); `expected_failures.txt` class
  `ruled`, quoting the ruling; the OCaml pin records the deviating
  reference, the Lean pin lem's semantics. Rulings record: X5 addendum in
  `2026-09-03_exception-case-rulings.md`; DESIGN's deviation list.

## Plants (each test fails on the before-fix binary)

Before-fix binary: `Lem 2026-05-01` (a scratch build of `git archive
5dfcd25`, so no git hash in its version string), run with its own
`library/`, every run under `timeout 60`. Verbatim, from
`plants.log`/`plants-compile.log` of the scratch directory (paths shortened):

```
== (a) item 1: test_contextual_keywords.lem on base
  exit 1: File ".../test_contextual_keywords.lem", line 140, character 44:   Syntax error
== (b) new negative probes on base (accepted, or hung = plant)
  neg_record_field_mk: exit 0 after 2 s
  neg_record_field_casesOn: exit 0 after 1 s
  neg_record_width_128: exit 0 after 2 s
  neg_variant_width_128: exit 124 after 60 s
  neg_tyvar_type_param_collision: exit 0 after 2 s
  neg_recup_reserved_base: exit 0 after 3 s
== (c) item 5: test_wide_patterns.lem on base
  exit 124 after 60 s
== (e) item 8: -outdir Makefile/sub on base
  exit 2: mkdir: cannot create directory ‘Makefile’: Not a directory Fatal error: exception Sys_error("Makefile/sub/Test_misc.lean: Not a directory")
== (d) items 2/3/4: generate with base, then compile against LemLib
  gen test_records: exit 0
  gen test_tyvar_collision: exit 0
  gen test_mutual_record_order: exit 0
== Test_records (generated by 5dfcd25) compiled against LemLib:
Test_records.lean:148:2: error: unexpected token 'at'; expected command
== Test_tyvar_collision (generated by 5dfcd25) compiled against LemLib:
Test_tyvar_collision.lean:52:50: error: Application type mismatch: The argument
Test_tyvar_collision.lean:54:53: error: Type mismatch
== Test_mutual_record_order (generated by 5dfcd25) compiled against LemLib:
Test_mutual_record_order.lean:259:26: error(lean.invalidField): Invalid field `hb_lo`: The environment does not contain `Nat.hb_lo`, so it is not possible to project the field `hb_lo` from an expression
```

Reading: (a) item 1 fails to parse before the fix. (b) five of the six new
negative probes are ACCEPTED before the fix (the suite's `lean-negative`
phase would report "FAIL (accepted)"); the sixth, the 128-argument
constructor, hangs in the old layout printer (its derived one-line output
is the item-5 shape), so before the fix it is neither refused nor
generated. (c) the wide-pattern test times out before the fix (the
`lean-wide-patterns` phase fails with exit 124). (e) before the fix the
`mkdir -p` failure is ignored and lem dies later on the temp-file rename
with `Sys_error`; the `lean-outdir-refusal` phase's grep for "cannot
create the output directory" fails. (d) the three extended positive tests
generate before the fix but their Lean does not compile: the bare `at`
field, the captured type variable, the unparenthesised update base. After
the fix every one of these is green in the suite run below. Item 10 is a
registration, not a fix: the probe's two pins are the before and after of
nothing; its plant is the suite's own rule that a registered probe which
PASSES fails the suite.

## Gates (verbatim tails)

All runs in the worktree, final binary (`lem -v`: see the suite's
`test_version` line), nothing rebuilt during a run (the first drift run
was invalidated by a concurrent rebuild — its fork side reported
`LEMROOT/lem: No such file or directory` — and re-run).

`scripts/ce make nonlean-regress` (tail, verbatim):
```
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
```

`scripts/ce env UPSTREAM_LEM=/home/dev/projects/linksem-lean/deps/lem-upstream LINKSEM=/home/dev/projects/linksem-lean/worktrees/linksem-upstream CERBERUS=/home/dev/projects/cerberus-lean-proj/deps/cerberus-upstream make upstream-drift DRIFT_OUT=<empty dir>` (head and the class summary, verbatim; the 32 library code rows are all "comments/whitespace only"; `cerberus-ocaml` and `linksem-ocaml` are absent from the per-directory counts, i.e. byte-identical — the same state the output-niceness record §13 recorded for `131b922`):
```
upstream-drift: upstream 3802cb0, fork lean-backend-v0.1.0-alpha.1-49-g5dfcd25-dirty; clients compared: linksem cerberus
upstream-drift: 944 upstream files; 198 differ (list: .../drift2/differences.txt)
     26 backends/tex_all
     11 lib/coq
      7 lib/hol
     26 lib/html
      1 lib/ident.stdout
      7 lib/isa
     26 lib/lem
      7 lib/ocaml
     84 lib/tex
      3 lib/tex_all
library code files (OCaml/HOL/Isabelle/Coq):
  comments/whitespace only  lib/coq/lem_basic_classes_auxiliary.v
  [… 32 such rows, no code row]
make: *** [Makefile:60: upstream-drift] Error 1
```
(The non-zero exit is the script reporting the fork's accepted non-code
library differences, as in every previous record.)

`cd lean-lib && capped lake build`: `Build completed successfully (39 jobs).`
`make` leaves the tree clean apart from the intended changes (`git status`
at commit time).

`scripts/ce make -C tests/comprehensive lean` (tail, verbatim):
```
test_version: OK (untagged, exact annotated tag, dirty tag, post-tag, archive fallback)
  OK: missing lean_constants refused; intact library generates
test_failure_admission: OK (registered probe with compiler failure is red, not XFAIL)
=== Wide patterns generate within 60 s (layout printer regression tripwire) ===
  OK: test_wide_patterns.lem generated in 4 s
=== Output directory that cannot be created is refused loudly ===
  OK: refused: cannot create the output directory Makefile/sub: Makefile/sub: Not a directory
=== Generation: 72 passed, 0 failed, 0 skipped ===
  [comments, layout, text-fidelity gates: OK; lean-compile: 768 PASS lines, no error]
  OK (leg 1): panic prints the Incomplete Pattern message, then continues with default
  OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1
  OK (leg 1): untaken branches not evaluated
  OK (leg 2): the taken branch fail-stops with its message
  OK (leg 3a): lemRequireAbortOnPanic refuses with LEAN_ABORT_ON_PANIC unset (exit 2)
  OK (leg 3b): lemRequireAbortOnPanic refuses LEAN_ABORT_ON_PANIC=0 (exit 2)
  OK (leg 3c): with LEAN_ABORT_ON_PANIC=1 the check passes and the failure fail-stops (exit 134)
  OK (leg 4): each reached Assert_extra.fail panics (2 of 2; B8 never_extract)
single-evaluation: OK
  OK: compiled draw sequences hold
  OK: compiled consumer injection holds
  OK: compiled N-ary seed injection holds
  OK (leg 1): two sufficient fuels agree; insufficient gives the declared sentinel; callee starts from the full ambient
  OK (leg 2): loud exhaustion at an insufficient runtime fuel fail-stops (exit 134)
  OK: compiled fuel x reader x mutual composition holds
  [lean-negative: 115 probes "OK (rejected as declared)", the six new ones included; lean-invariance: 10 witnesses "artifacts byte-identical across ocaml/hol/isa/coq"]
parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
=== No sorry/admit/axiom/native_decide in fuel_measure proofs modules (gate) ===
  OK: 11 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
=== No fuel numerals in LemLib or generated code (gate) ===
  OK: 322 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
suite exit 0
```
(Bracketed lines are derived summaries of blocks of identical OK lines; every
other line is verbatim. The parity count is 38 OK + 11 XFAIL: the ten
registered probes before this slice plus `p_user_ord_minmax`.)

## Consumer trees

Both frozen consumers regenerated with the final `lem` of this branch and
compared with the trees generated by the unmodified `5dfcd25` binary from
the same inputs: Cerberus 170 files, linksem 194 files, **byte-identical**
(`diff -rq`: 0 differing files; `tokdiff.py`: identical). No census was
needed. This is expected: every change either refuses input that failed
today, renames or escapes only on collisions neither consumer has, or
(the layout printer) makes the same decisions faster.

## Files

- `src/parser.mly` (item 1), `src/lean_layout.ml` (item 5),
  `src/process_file.ml` (item 8), `src/lean_backend.ml` (items 2, 3, 4, 6,
  8, 9).
- Tests: `tests/comprehensive/test_contextual_keywords.lem`,
  `test_records.lem`, `test_mutual_record_order.lem`,
  `test_tyvar_collision.lem` (new), `test_wide_patterns.lem` (new),
  `negative/neg_record_field_mk.lem`, `neg_record_field_casesOn.lem`,
  `neg_record_width_128.lem`, `neg_variant_width_128.lem`,
  `neg_tyvar_type_param_collision.lem`, `neg_recup_reserved_base.lem`
  (all new), `parity/probes/p_user_ord_minmax.lem` + its two pins,
  `parity/expected_failures.txt`, `lean-test/lakefile.lean` (two roots),
  `Makefile` (phases `lean-wide-patterns`, `lean-outdir-refusal`).
- Docs: `DESIGN.md`, `TODO.md` (37 closed; 45–48 added), `RECORDS.md`,
  `2026-09-03_exception-case-rulings.md` (X5), `doc/manual/backend_lean.md`.

## Left for the operator

- Item 7's general fix waits on the `BEq` bridge design pass (TODO 45/46).
- TODO 47: whether type-definition parameters should be renamed rather
  than refused, and whether to narrow the `below`/`brecOn` field refusal to
  recursive records.
- Package C (cleanup, no output change), including the walker
  consolidation the item-3 collector adds to (TODO 48).

## Provenance

[USER 2026-10-03]: the rulings quoted above. [AGENT] (this worker): every
measurement, the escape/refuse split of item 2, the rename/refuse split of
item 3, the primed fresh names, the reserved `lemRecBase`, the 127-field
limit as a count, the item-7 disposition, the tests and this record.

## Orchestrator verification of package A (2026-10-03)

The orchestrator re-ran the gates independently on `f33cf4f`, from the
frozen inputs (Cerberus `51a7402ce`, linksem `f54d119` source export):
```
base make exit 0 / arc make exit 0   [tree clean after make]
cerb: 0 differing files / linksem: 0 differing files   [vs 5dfcd25's lem]
lemlib exit 0  (Build completed successfully (39 jobs).)
=== Generation: 72 passed, 0 failed, 0 skipped ===
Build completed successfully (206 jobs).
parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
upstream-drift: 944 upstream files; 198 differ   [library code rows all comments/whitespace only; cerberus-ocaml / linksem-ocaml absent]
```

**Rulings since the slice began**, all [USER 2026-10-03]:
- #2 (the `BEq` bridge): option (a), 450/400 (the recommended one), landing as its
  own slice after A and C. Design note: branch `docs/beq-lattice-design`, `39c4e0c`.
  TODO 45 (`automatic` termination under the bridge) is retested in that
  slice.

**Attribution note.** The operator agreed this is minor but is to be got
right from now on: `Co-Authored-By` trailers name the model that actually did the work.
- `f33cf4f` correctly says Claude Fable 5.1.
- The earlier Fable-written output-niceness commits `ac5565b`, `131b922` and
  `0885bf6` say Claude Opus 5.5, because the orchestrator's brief prescribed
  that line. They are merged and pushed, so they stay as they are; this note
  is the correction.

## Package C: cleanup, no output change (2026-10-03)

Ruling [USER 2026-10-03]: package C (cleanup, no output change), the
recommended option. Worked on `arc/backend-hardening` from `a1fdf6e` (package A
verified). Every decision below not quoted as a ruling is [AGENT]. The
source is the code review of 2026-10-03 (`REPORT.md` §3–§7 and its notes);
every claim acted on was re-verified first (grep, build, or a run).

Commits: `a6c63aa` (1/4: dead code, the reserved-name table, the priority
constant, the debug variables), `35e893e` (2/4: LemLib deletions), `cff6663`
(3/4: comments and messages, the TODO 39 test), the commit that adds this section (4/4: TODO
register and this record). Gates ran on every commit's tree, with the lem
binary built from it (§"Gates" below).

### 1. Dead code (backend and the fork's shared-file edits)

Each deletion had zero callers over `src/`, `library/`, `tests/`,
`lean-lib/` (grep; counts are of hits other than the definition itself):

| Deleted | Evidence |
|---|---|
| `is_fuelled_cref` (`lean_backend.ml`) | 0 hits |
| `tv_reason` + `let _ = tv_reason`, `fallback_beq_ord`, `fallback_trio` and their "RETIRED" comments | both `fallback_*` were `emp` spliced into the instance output: 0 bytes of output; `tv_reason` read only by `let _` |
| `block`/`block_hov` no-op wrappers and their three call sites (`Fun`, `Set`, `Vector` renderers), plus the `is_user_exp` binding only they read | wrappers were `fun _ _ t -> t` (shadowing `Output.block`); unwrapped in place |
| `let _ = t in` (`derived_comparison_single`: the pattern variable is now `_`), `let _ = if … in` (now a statement) | no value read |
| `open Backend_common` | every use qualified (compiles without it) |
| `Output.flatten_newlines`, `flatten_newlines_in_comment` (`src/output.ml`, `.mli`) | fork-introduced (`git show 3802cb0:src/output.ml` has neither); the backend aliases `flatten_newlines_keep_comments` — 0 callers |

Not deleted: `St.reset_invocation` (no caller, but TODO item 6's threading
work is its home; unchanged since package A).

### 2. LemLib deletions (consumer-visible)

Read-only greps over all consumers — `cerberus-lean/lean_frontend/*.lean`
(49 files), `cerberus-sl` (12 301 `.lean` files outside `.lake`),
`linksem-lean/linksem/lean/{handwritten,driver}` — and over lem-lean itself
(`library/`, `tests/`, `lean-lib/`, `src/`). Counts are hits per consumer
(cerberus-lean / cerberus-sl / linksem):

| Deleted | Consumer hits | lem-lean hits |
|---|---|---|
| `natDiv`, `natMod` (silently total `a / b`, `a % b`) | 0 / 0 / 0 | 0 — `num.lem` points every rep at `lemNatDiv`/`lemNatMod` |
| `unsupportedRationalFromNumeral/FromInt/FromFrac`, `unsupportedRealFromNumeral/FromInt/FromFrac` (root duplicates of `LemUnsupported.*`) | 0 / 0 / 0 | 0 — `num.lem` uses the `LemUnsupported.` twins; the `*Less/LessEq/Greater/GreaterEq/Abs` wrappers stay (used by the generated `Num.lean`) |
| `lemBoolToProp` | 0 / 0 / 0 | 0 |
| `apply` | 53 / 209 / 0 — all the tactic `apply` or prose (filtered by hand; `function.lem:59` inlines lem's `apply` on Lean, so no generated code can reference the root def) | 0 |
| `listGet?`, `listGet!` | 0 / 0 / 0 | 0 (`listGetOpt`/`listGetBang` are the live pair, `list.lem:495`, `list_extra.lem:122`) |
| `listSet` (its comment "replaces removed List.set" was false: the body called `List.set`) | 0 / 0 / 0 | 0 |
| `setPartitionBy` | 0 / 0 / 0 | 0 (`set.lem` has no `partition` rep) |
| `Pmap.mem`, `maxBinding?`, `exists_`, `filter`/`filterAux`, `partition`/`partitionAux`, `compare`/`compareAux` | 0 / 0 / 0 (the consumers' `Pmap.` uses: `Empty`, `Node`, `find?`, `find`, `bindings(Aux)`, `add`, `map`, `fold`, `empty`, `CmpLaws`) | 0 outside their own recursion; `map.lem:233`'s `Pmap.mem` is the OCaml rep |
| `lemListMapiAux` and its theorem `lemListMapiAux_eq` (`LemLibTheorems.lean`) | 0 / 0 / 0 | only the theorem |

Also: the stale `LemLibPmapLaws.lean` comment that explained writing
`Ord.compare` to avoid `Pmap.compare` (gone). The regenerated
`lean-lib/LemLib/*.lean` are unchanged (they come from `library/*.lem`,
untouched).

Kept, deliberately: `lemNatLnot`/`lemNatLsr` (TODO item 33 is an operator
decision; `lemNatLsr` added to the row); `lemStringFromNatHelper`/
`NaturalHelper` and the `partial` `natSqrtAux` (TODO item 38: merging or
totalising changes a definition, not a deletion); the `OfNat` instances on
the unsupported types (review suspicion, unmeasured). Comments in
`library/*.lem` (jargon at `set.lem:350`, `relation.lem:629`, `map.lem:80`,
`word.lem:855`, `function.lem`'s wrong line number) were NOT touched: every
`.lem` comment is carried into the nine non-Lean outputs, so the change
would move `nonlean-regress`'s goldens and need a rebaseline — left for a
slice that rebaselines.

### 3. Comments

`src/lean_backend.ml`: 184 replacements (a scripted sweep, each old text
matched exactly once), plus `src/lean_layout.ml` (4), `src/parser.mly`
(3 comment/message sites), `lean-lib/LemLib.lean` (48, plus the `fmapUnionBy` binder),
`LemLibTest.lean` (8), `LemLibTheorems.lean` (3), `LemLibPmapLaws.lean`
(4), `lakefile.lean` (3), `lean-lib/README.md` (1). What changed: arc,
slice, charter, audit and finding tags (`arc-14 S2 B1 (be:G3)`, `linksem
2026-09-28 (B13)`, `parity-fix F5/F6`, `D2-enablers slice`), dates that
narrated history, the `A' witness: use2 100 (1,2) = 5` style of evidence,
the two `HISTORY` blocks of `LemLib.lean` (now one plain "no axiom, no
unsafe inhabitant" note naming what was removed and why), "verbatim port"
(the translations are not verbatim: NOTICE/DESIGN). Kept: every `[USER …]`
ruling quote and every pointer to a design note or to a record where a
ruling is the reason (`2026-08-22_arc14-instance-priority-lattice.md`,
`arc8-inhabited-threading-design.md`, `2026-09-05_measure-hypothesis-record.md`,
`2026-09-01_L2-deletion-record.md`, `2026-09-03_exception-case-rulings.md`),
and the mechanism comments the review named as the model.

Corrected claims: the stale "sorry" wording — the `lean_cmp_shape`
parameter `sorried` and the derivation's `sorried`/`sorried0` variables
are `residual`/`residual0` (the instances are loud `failwithI` residuals,
not `sorry`), and the comment for `lean_cmp_shape` now sits on its
function (it was separated from it by `lean_typ_has_fn`); "the proof is by
sorry anyway" (theorem marker), "sorry-based opaque type instances",
"skip sorry BEq/Ord instances", "sorried residual instances",
"sorry-based instances are useless" — all rewritten to what the code does.
The wrong claim at the `Infix` renderer ("this Infix path has NONE of the
reader/fuel hooks" while `fuel_scope_check` is called four lines below) now
says which checks run there (unsupported construct, supply, fuel scope,
reader_consumer) and which injection hooks are absent (reader arguments,
the fuel worker rewrite), and why a fuel'd constant still resolves (the
`[LemFuel]` binder is instance-implicit). The header's "BEq is derived for
types without function-typed constructor args" and "Block formatting is
disabled" rows describe the current derivation and layout passes.

### 4. User-facing messages

Rewritten to plain, actionable English; every negative probe's `EXPECT`
substring kept unless noted:

| Site | Was | Now |
|---|---|---|
| `declare {lean} effectful` refusal | "deleted by the effect-retirement arc (charter: cerberus-lean lean_frontend/docs/2026-08-31_effect-retirement-design.md @64dd6efeb, section 7.1)" | "…crossed from BaseIO back into pure types through a library axiom, which is gone (doc/lean-backend/DESIGN.md, \"Zero axioms; effects as explicit state\")"; EXPECT `'declare {lean} effectful' is retired on the lean target` kept |
| FM-literal (numeral measure) | quoted the [USER 2026-09-03] ruling verbatim | "a literal fuel is a magic value, forbidden by design — doc/lean-backend/DESIGN.md, \"No magic values\""; EXPECT `FM-literal` kept |
| reserved-name capture | "(pre-merge audit 2026-09-05, probe p11b)"; listed five names | the names come from the table (now including `lemRecBase`); the cite is gone; EXPECTs `renders on Lean as \`lemFuel\` — a reserved synthesized binder name` / `\`lemTail\`` kept |
| reserved binder | listed the names inline | from the table (the same three names and two prefixes); EXPECTs kept |
| Type-1 comparison refusal | "(the historical sorry-bodied residual instances are deleted, arc-10 audit fix)" | "…in the Type 1 universe, where the comparison classes are not defined; escape hatches: …". `neg_type1_comparison.lem`'s EXPECT was the WHOLE old message; it is now the diagnosis `cannot derive BEq/Ord instances for type 't1': heterogeneous type-parameter counts put its mutual block in the Type 1 universe` (justification: the removed clause was the process history itself; the new substring still pins the reason and the type name) |
| `Te_opaque` internal error | "(opaque types are fail-closed, arc-8 S2)" | "internal error — … (opaque types are fail-closed)" |
| tuple-instance walk depth, confusable tuple-instance demand (×3), numeric type variable | "B14" | plain ("the tuple-instance walk", "local instance binding") |
| `let _ = e1`/`let () = e1` in a supply-threaded body | "(B15: e1 would be dropped; …)" | "(e1 would be dropped; …)" |
| `parser.mly` numeric fuel budget | "was removed (fuel-parameter arc, 2026-09-04) … [USER 2026-09-03] \"…\"" | "is not accepted: a per-declaration fuel literal is a magic value (doc/lean-backend/DESIGN.md, \"No magic values\") … Use the sentinel form"; EXPECT `numeric fuel-budget form` kept |
| `parser.mly` numeric fuel measure | quoted the ruling; suggested `` `sizeOf x` `` (which the backend refuses: FM-sizeOf) | cites DESIGN; suggests `` `List.length xs + 1` ``; EXPECT `a numeral is not a fuel measure` kept |

### 5. TODO register

- 39 closed: `is_lean_pat_direct` exists (`src/patterns.ml`), the path is
  reachable, and `tests/comprehensive/test_multiclause.lem` + the suite
  phase `lean-multiclause` pin the equation form (`def f : Nat → Nat | (0 :
  Nat) => 1 | (n : Nat) => n`, the cons form for `len2`) and the single
  `match` for a constructor-pattern group, with asserts for the values.
- 38 rewritten: four `partial def`s (the generated
  `Lem_Set_extra.leastFixedPointUnbounded` added; `natSqrtAux` marked
  avoidably partial), the helper duplication, and what package C deleted.
- 34 measured: 18 of 259 root-level declarations of `LemLib.lean` are in
  `lean_constants`, 241 absent (awk over the file, before the deletions;
  the review's "about 300" overstated it); `LemLib` itself is the exposed
  root of `supplySplit`.
- 36: (e) `initial_env.ml` and (f) `type_defs_rename_type` added, with the
  (b)↔(d) coupling.
- 33: `lemNatLsr` added, with why (`transform.lem` is not in `LIBS`).
- 3/4/6/29: line references re-derived by grep after the sweep; 4 lists
  the review's further name-keyed sites; 6 notes the callback fires on
  every target.

### 6. Debug variables

`LEM_INH_DEBUG`, `LEM_THREAD_DEBUG`, `LEM_LEAN_LAYOUT_DEBUG` are documented
in DESIGN ("Debugging the analyses": what each prints). The two backend
ones are read with `Sys.getenv_opt … <> None` like the layout one, so all
three mean "set to any value" (before, `LEM_INH_DEBUG=` — set but empty —
was off; a debug knob, no output effect).

### 7. Small duplications

- The reserved-name contract is one table (`lean_reserved_*` in
  `lean_backend.ml`, with `lean_starts_with`): the binder check, the
  capture check, `lemLetRhs_`, `_lemIfTail`, `lemSize`/`lemSize_aux` and the
  `lemTail`/`lemRecBase` literals read from it; the inline prefix-length
  literals (`11`, `10`) are gone. Behaviour: UNCHANGED. The five sites had
  not drifted by accident: the binder check deliberately omits `lemTail`,
  because the tail hoisting (`lean_hoist_tail_binders`, which runs first)
  synthesizes that binder into the very clause the check scans — the first
  attempt at a full union refused Cerberus's `are_compatible`
  (`ailTypesAux.lem:784`, "binder 'lemTail' collides…"). The table records
  the two populations (`lean_reserved_binder_names` ⊂
  `lean_reserved_exact_names`) and the reason. The capture check's message
  gained `lemRecBase`, which it checked but did not list.
- `(priority := 500)` at six sites is `lean_instance_kw_auto`
  (`lean_instance_auto_priority = 500`); the emitted text is byte-identical
  (consumer trees). The BEq-lattice slice changes one constant.
- `fmapUnionBy`'s unused comparator binder is `_cmp` (one LemLib build
  warning fewer; no term change).

### Gates (verbatim tails)

Reference trees: `.tmp/hardening/v-arc/` (package A's output from the
frozen inputs). Builds of `lem` are the worktree's; every Lean run through
`cerberus-lean/scripts/capped`.

Commit 1 (`a6c63aa`), binary built from it:
```
cerb: 0 differing files
linksem: 0 differing files
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
=== Generation: 72 passed, 0 failed, 0 skipped ===
Build completed successfully (206 jobs).
parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
suite exit 0
upstream-drift: upstream 3802cb0, fork lean-backend-v0.1.0-alpha.1-51-ga1fdf6e-dirty; clients compared: linksem cerberus
upstream-drift: 944 upstream files; 198 differ (list: …/v-drift-c1/differences.txt)
```
(115 negative probes "OK (rejected as declared)", 10 invariance witnesses;
the drift library code rows: 32, all "comments/whitespace only";
`cerberus-ocaml`/`linksem-ocaml` absent, i.e. byte-identical.)

Commit 2 (`35e893e`), LemLib only (the lem binary is commit 1's, so the
consumer trees, nonlean-regress and the drift check are unchanged by
construction):
```
Build completed successfully (39 jobs).
=== Generation: 72 passed, 0 failed, 0 skipped ===
Build completed successfully (206 jobs).
parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
suite exit 0
```
(115 negative probes rejected as declared, 10 invariance witnesses; the
LemLib build's 5 unused-variable warnings are the pre-existing ones.)

Commit 3 (`cff6663`), binary rebuilt from it:
```
cerb: 0 differing files
linksem: 0 differing files
Build completed successfully (39 jobs).
=== Generation: 73 passed, 0 failed, 0 skipped ===
=== Multi-clause definitions render as Lean equations (TODO item 39 pin) ===
  OK: equation form for f and len2, match form for g
Build completed successfully (208 jobs).
  OK (rejected as declared): negative/neg_type1_comparison.lem
parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
suite exit 0
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
upstream-drift: upstream 3802cb0, fork lean-backend-v0.1.0-alpha.1-53-g35e893e-dirty; clients compared: linksem cerberus
upstream-drift: 944 upstream files; 198 differ (list: …/v-drift-c3/differences.txt)
```
(115 negative probes rejected as declared, 10 invariance witnesses, the
five `mc_*` asserts PASS; LemLib 4 warnings, was 5; the drift library code
rows: 32, all "comments/whitespace only", `cerberus-ocaml`/`linksem-ocaml`
absent. The "FAIL:" lines the parity runner prints inside the registered
XFAIL probes are its own reporting of the pinned Lean side.)

Compiler warnings (clean `ocamlbuild -clean` + `make`, default flags):
29 before (`a1fdf6e`), 29 after; none in `lean_backend.ml`,
`lean_layout.ml`, `output.ml`, `parser.mly` (the 29 are upstream's). LemLib:
5 "variable not explicitly referenced" warnings before, 4 after
(`fmapUnionBy`'s `cmp`; the other four are copied from `.lem` pattern
variables, review L3).

### Provenance

[USER 2026-10-03]: the package ruling. [AGENT]: every deletion decision,
the reserved-name-table population split, the message wordings, the TODO
texts, the kept items and this record.

## Orchestrator verification of package C (2026-10-03)

The orchestrator re-ran the gates independently on `1ecf93f`, from the same
frozen inputs:
```
arc make exit 0   [tree clean after make]
cerb: 0 differing files / linksem: 0 differing files   [vs 5dfcd25's lem]
lemlib exit 0  (Build completed successfully (39 jobs).)
=== Generation: 73 passed, 0 failed, 0 skipped ===
  OK: equation form for f and len2, match form for g
Build completed successfully (208 jobs).
parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
upstream-drift: 944 upstream files; 198 differ   [library code rows all comments/whitespace only; cerberus-ocaml / linksem-ocaml absent]
```
Deleted LemLib definitions: a spot check of `natDiv`, `natMod`,
`lemBoolToProp`, `listGet?`, `listGet!`, `setPartitionBy`, `lemListMapiAux`
and `unsupportedNatFrom` finds no use in hand-written consumer Lean
(Cerberus `lean_frontend/*.lean`, cerberus-sl, linksem handwritten/driver).
The same names, plus `listSet` and the `Pmap` mirrors, have no use in the
regenerated consumer trees either.

## BEq-lattice slice: the `[Eq0 a] : BEq a` bridge below core (2026-10-03)

Rulings [USER 2026-10-03]: option (a), 450/400 (the recommended one), and
its own slice after A and C. The design pass it lands is
[`2026-10-03_beq-instance-lattice-design.md`](2026-10-03_beq-instance-lattice-design.md)
(code-review finding L1, TODO item 46). Worked on `arc/backend-hardening`
from `8666b7f` (packages A and C verified). Every decision below that is
not one of the rulings is [AGENT]. Lean 4.32.2; every Lean run through
`cerberus-lean/scripts/capped`; consumer inputs frozen as in packages A
and C (Cerberus `51a7402ce`, linksem `f54d119`); scratch under
`.tmp/hardening/beq/` (ephemeral, deleted at slice end).

### 1. The change

`src/lean_backend.ml`: the one priority constant of package C became a
three-row table beside the lattice comment — `lean_instance_auto_priority
= 500` (unchanged), `lean_instance_eq0_bridge_priority = 450`,
`lean_instance_comparator_bridge_priority = 400` — with one keyword
builder `lean_instance_kw`. The class emitter's two bridge sites use the
two new rows: the `[Eq0 a] : BEq a` bridge, which was emitted with no
priority (Lean's default 1000), and the comparator-derived
`[SetType a]`/`[MapKeyType a] : BEq a` bridges, which were at the auto
slot. `make` regenerated the library; `git diff lean-lib/` is exactly the
three priority lines (verbatim):

```
-instance { a : Type } [Eq0 a] : BEq a where
+instance (priority := 450) { a : Type } [Eq0 a] : BEq a where
-instance (priority := 500) { a : Type } [SetType a] : BEq a where
+instance (priority := 400) { a : Type } [SetType a] : BEq a where
-instance (priority := 500) { a : Type } [MapKeyType a] : BEq a where
+instance (priority := 400) { a : Type } [MapKeyType a] : BEq a where
```

(`Basic_classes.lean:32`, `:184`; `Map.lean:55`.) Both consumer trees
regenerated with the changed `lem` are byte-identical to the trees from
`8666b7f`'s `lem` (`diff -rq`: `cerb: 0 differing files`, `linksem: 0
differing files`; 170 and 194 files).

### 2. The lattice, measured before and after

Against LemLib at `8666b7f` (`#synth`, `pp.explicit`), verbatim:

```
@instBEqOfEq0 Nat Lem_Num.instEq0Nat_1
@instBEqOfEq0 Int Lem_Num.instEq0Int_1
@instBEqOfEq0 String instEq0String
@instBEqOfEq0 Char instEq0Char
@instBEqOfEq0 Bool instEq0Bool
@instBEqOfEq0 Unit instEq0Unit
@Lem_Map.instBEqOfMapKeyType Int8 (@Lem_Map.instMapKeyTypeOfSetType Int8 (@instSetTypeOfOrd Int8 Int8.instOrd))
@instBEqOfEq0 Int32 Lem_Num.instEq0Int32
@instBEqOfEq0 Int64 Lem_Num.instEq0Int64
@Lem_Map.instBEqOfMapKeyType UInt64 (@Lem_Map.instMapKeyTypeOfSetType UInt64 (@instSetTypeOfOrd UInt64 UInt64.instOrd))
instBEqLemOrdering
Lem_Word.instBEqBitSequence
@List.instBEq Nat (@instBEqOfEq0 Nat Lem_Num.instEq0Nat_1)
ProbeOld.lean:57:0: error: failed to synthesize
  @LawfulBEq Nat (@instBEqOfEq0 Nat Lem_Num.instEq0Nat_1)
```

The Eq0 bridge won at Nat, Int, String, Char, Bool, Unit, Int32, Int64; the
comparator bridge (`instBEqOfMapKeyType`, the newer of the two tied with
core at 500) won at Int8, Int16, ISize, UInt8, UInt16, UInt32, UInt64,
USize, `BitVec n` and core's `Ordering`. Derived (`LemOrdering`,
`bitSequence`) and specific (`List`, `Option`, `Prod`, `Pset`, `Fmap`,
`Sum`) instances were not displaced, only their base-type arguments. The
old base `Eq0` bodies, verbatim `#print` (the Int, Int32, Int64, String,
Char and Bool instances have the same shape over their `Ord`):

```
def Lem_Num.instEq0Nat : Eq0 Nat :=
@Eq0.mk Nat (fun x y => @BEq.beq Nat (@instBEqOfSetType Nat (@instSetTypeOfOrd Nat instOrdNat)) x y) …
def Lem_Num.instEq0Nat_1 : Eq0 Nat :=
@Eq0.mk Nat (fun x y => @BEq.beq Nat (@instBEqOfEq0 Nat Lem_Num.instEq0Nat) x y) …
def instEq0Unit : Eq0 Unit :=
@Eq0.mk Unit (fun x x_1 => true) fun x x_1 => false
```

After the change every one of those seventeen types resolves to
`@instBEqOfDecidableEq T instDecidableEqT` (verbatim for the three the
probe names: `instBEqOfDecidableEq` ×3; `LawfulBEq`: `Nat.instLawfulBEq`,
`instLawfulBEqString`, `@instLawfulBEq UInt64 instDecidableEqUInt64`), the
base `Eq0` bodies re-elaborate to core
(`instEq0Nat_1 := @Eq0.mk Nat (fun x y => @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) x y) …`),
and `@instBEqOfEq0 Nat Lem_Num.instEq0Nat_1 = instBEqOfDecidableEq` holds by
`rfl` at all seven Eq0-route types. `Std.LawfulEqOrd` exists in core for
every switched type except `Unit` (LemLib's own `instOrdUnit_lemLib`) and
`Ordering`.

### 3. Probes, plant-tested

`tests/comprehensive/lean-test/TestInstancePriorityCheck.lean` gained legs
5 and 6: `#guard_msgs in #synth BEq Nat/String/UInt64` expecting
`instBEqOfDecidableEq`; `LawfulBEq` at the three types by `inferInstance`;
the operator's example `(a b : Nat) (h : (a == b) = true) : a = b := by simpa
using h` (and at `String`); `(a == b) = decide (a = b) := rfl` at `Int`; a
model-only inductive still resolving to `instBEqOfEq0`; polymorphic
`[Eq0 a] [SetType a]` code resolving to the Eq0 bridge (`rfl` against
`isEqual`). Legs 1–4 are unchanged. The plant compiled the file with the
generated `Test_instance_priority` against the `8666b7f` LemLib in a scratch
Lake project; every leg-5 line fails, legs 1–4 and 6 pass (verbatim, the
nine errors):

```
error: TestInstancePriorityCheck.lean:63:0: ❌️ Docstring on `#guard_msgs` does not match generated message:
- info: instBEqOfDecidableEq
+ info: instBEqOfEq0
error: TestInstancePriorityCheck.lean:65:0: ❌️ Docstring on `#guard_msgs` does not match generated message:
- info: instBEqOfDecidableEq
+ info: instBEqOfEq0
error: TestInstancePriorityCheck.lean:67:0: ❌️ Docstring on `#guard_msgs` does not match generated message:
- info: instBEqOfDecidableEq
+ info: Lem_Map.instBEqOfMapKeyType
error: TestInstancePriorityCheck.lean:68:27: failed to synthesize instance of type class
  LawfulBEq Nat
error: TestInstancePriorityCheck.lean:69:30: failed to synthesize instance of type class
  LawfulBEq String
error: TestInstancePriorityCheck.lean:70:30: failed to synthesize instance of type class
  LawfulBEq UInt64
error: TestInstancePriorityCheck.lean:72:56: Type mismatch: After simplification, term
  h
 has type
  (a == b) = true
but is expected to have type
  a = b
error: TestInstancePriorityCheck.lean:73:59: Type mismatch: After simplification, term
  h
 has type
  (a == b) = true
but is expected to have type
  a = b
error: TestInstancePriorityCheck.lean:74:51: Type mismatch
  rfl
has type
  ?m.7 = ?m.7
but is expected to have type
  (a == b) = decide (a = b)
```

The same project against the changed LemLib: `Build completed successfully
(36 jobs).` These legs are speedbumps on the elaboration property; the
trust property, value parity, is §4.

### 4. Agreement theorems (`lean-lib/LemLibTheorems.lean`, namespace `BeqLattice`)

For every type whose winner switched, a kernel theorem states the OLD
instance term — spelled out, since it no longer wins resolution — equal to
the NEW one. `cmpBEq_eq_decide` (`[Ord α] [Std.LawfulEqOrd α] [DecidableEq α]`:
the comparator route `match defaultCompare a b with | .EQ => true | _ =>
false` equals `decide (a = b)`) and its two instance-form corollaries
`setTypeBridge_eq_core` (the Eq0 route's old body:
`@instBEqOfSetType α (@instSetTypeOfOrd α _)`) and `mapKeyBridge_eq_core`
(`@instBEqOfMapKeyType α (@instMapKeyTypeOfSetType α (@instSetTypeOfOrd α _))`);
then per type, with the instance names as `#print`/`#synth` gave them:
`nat_old_eq_new`, `int_`, `string_`, `char_`, `bool_`, `int32_`,
`int64_old_eq_new` (Eq0 route), `unit_old_eq_new` (old body `true`, by
cases), `int8_`, `int16_`, `isize_`, `uint8_`, `uint16_`, `uint32_`,
`uint64_`, `usize_`, `bitVec_old_eq_new` (`∀ n`) and `ordering_old_eq_new`
(by cases; core has no `LawfulEqOrd Ordering`) for the comparator route. The
new state is pinned by `rfl`: `isEqual_nat`/`_nat_1`/`_int`/`_int_1`/
`_int32`/`_int64`/`_string`/`_char`/`_bool` (`Eq0.isEqual a b = decide (a =
b)`), `isEqual_unit` (by cases) and `bridge_<T>_is_core`
(`@instBEqOfEq0 T instEq0T = instBEqOfDecidableEq`) for the seven Eq0-route
types. `#print axioms` (build log, verbatim shape): `cmpBEq_eq_decide`,
`setTypeBridge_eq_core`, `mapKeyBridge_eq_core`, `bool_old_eq_new`,
`ordering_old_eq_new` depend on `[propext]`; `unit_old_eq_new` and
`isEqual_unit` on none; every other `*_old_eq_new` on `[propext,
Classical.choice, Quot.sound]` (through core's `LawfulEqOrd` instances). No
`native_decide`, `bv_decide`, `ofReduce*`, `decide`, `sorry`.

Coverage of the census pairs (§5): every `(Nat, Lem_Num.instEq0Nat_1)` site
and its abbreviations (`aid`, `thread_id`, `thread_id0`, `allocation_id`,
`loop_id`, `tid`, `reg`, `scope_id`, `provenance_id`; linksem `cfa_*`,
`address_expr_fn_ref`) → `nat_old_eq_new`; `(Int, instEq0Int_1)` and
`CerbMem.StorageInstanceId`/`Address`/`SymbolicStorageInstanceId`,
`cfa_sfoffset`, `integer_value_base` → `int_old_eq_new`; `(String,
instEq0String)`, `sym`, `cabs_identifier` → `string_old_eq_new`; Bool, Char,
Int32, Int64 → their theorems; `(Unit, instEq0Unit)` and
`sdt_unspecified_parameter` → `unit_old_eq_new`; UInt8/UInt32/UInt64 and
`Ordering` comparator sites → `uint*_old_eq_new`, `ordering_old_eq_new`. The
two consumer-model pairs: Cerberus `(String, instEq0String_symbol)`, body
`@BEq.beq Int (@instBEqOfEq0 Int Lem_Num.instEq0Int_1) (digest_compare x y) 0`
(verbatim `#print`), is `int_old_eq_new` at its one `==` plus Cerberus's own
`CerbCtypeMeasure.digest_compare_eq_zero_iff`, which rebuilt green in the
after-census; linksem's `(Nat | uint32 | uint64, instEq0Uint64_elf_types_native_uint_2)`
and the nine other `instEq0Uint{32,64}_elf_types_native_uint*` are a chain of
`isEqual := fun x y => x == y` bodies (verbatim `#print`: `_2 → Uint32 _6 →
_5 → Uint64 _1 → Uint32 _4 → _3 → _2 → Uint64 → Uint32 _1 → Uint32 →
Lem_Num.instEq0Nat_1`), so every one is `nat_old_eq_new`. In linksem even
plain `Nat` resolved to that model instance (`#synth BEq Nat ⟶
@instBEqOfEq0 Nat instEq0Uint64_elf_types_native_uint_2`: `uint64` is a
reducible abbreviation of `Nat`); it is core now.

### 5. Census

Instrument: `Census3.lean` (scratch; Census2 plus instance normalisation and
site records). For every constant of the consumer modules it records the
type/value hashes, the same hashes after replacing every application of
`instBEqOfEq0`, `instBEqOfSetType`, `instBEqOfMapKeyType` or
`instBEqOfDecidableEq` by one marker (hygienic names canonicalised by the
NORMALISED hashes, so a helper whose only change is the switch keeps its
name), the binder signature, safety, reducibility hints and status,
instance/projection/inline/extern/matcher flags, and one `SITE` row per
instance application. A declaration is EXPLAINED when its raw hashes moved
and its normalised hashes did not. Both consumers were built from scratch
copies (Cerberus's `lean_frontend` with the frozen generated tree and the 49
hand-written files of `51a7402ce`; linksem's `lean/` with the frozen
generated tree, `gen-roots.sh` re-run), with the LemLib dependency pointed by
path first at a `git archive 8666b7f lean-lib` copy, then at this worktree's
`lean-lib`.

**Cerberus** (218 `CerberusLean` roots; before 22:26:32–22:29:24 and after
22:44:47–22:45:06, `Build completed successfully (252 jobs).` both; the
after-build with the §6 patch). Verbatim census tails:
`census3: 34087 constants in 218 modules (146 hygienic, 3 rounds, 2587 instance sites)`
before, `34083 constants … 2587 instance sites` after (122 identical hygienic
twins collapse to one canonical name in each; 33965/33961 distinct). Derived
comparison: 33961 common; 4 only-before (the old `natEq0_iff` proof's
`match_1`, `_sparseCasesOn_1`, `_proof_1_4`, `_proof_1_5`); **675
declarations changed** (590 `def`, 82 `thm` — statements only, proofs
unmoved — 1 `opaque` `CabsImport.positionFiles`, the private `CoreParser.ScanSt`
constructor and recursor, whose types mention `==` at `UInt64`); **675
explained, 0 not**; 493 in generated modules, 182 in hand-written ones
(`CerbMem` 53, `CoreParser` 42, `Core_aux_lemMeasureProofs` 28, the other
measure-proof modules, `CabsImport` 8, …; all compiled unchanged except §6);
0 in `_auxiliary` modules. 1971 further declarations differ only in their
reducibility-hint height (`h=regN`), the expected consequence of a different
instance in the dependency cone. The 2448 instance sites inside the changed
declarations are all `instBEqOfDecidableEq` after; the 44 polymorphic bridge
sites (type a bound variable) are unchanged; no bridge site at a named type
remains. Switched pairs (sites / declarations, derived):

```
  859 / 335  instBEqOfEq0 @ Nat / Lem_Num.instEq0Nat_1
  753 / 232  instBEqOfEq0 @ Int / Lem_Num.instEq0Int_1
  342 / 133  instBEqOfEq0 @ String / instEq0String_symbol
  162 / 100  instBEqOfEq0 @ Bool / instEq0Bool
   79 /  23  instBEqOfEq0 @ Char / instEq0Char
   48 /  19  instBEqOfMapKeyType @ UInt64
   46 /  19  instBEqOfEq0 @ Unit / instEq0Unit
  120 /  46  instBEqOfEq0 @ aid, thread_id, allocation_id, loop_id, tid, reg, scope_id, provenance_id, thread_id0 / instEq0Nat_1
   28 /  16  instBEqOfEq0 @ CerbMem.StorageInstanceId, Address, SymbolicStorageInstanceId / instEq0Int_1
    7 /   6  instBEqOfEq0 @ String / instEq0String
    5 /   4  instBEqOfMapKeyType @ UInt8, UInt32
```

**linksem** (97 generated + 97 `_auxiliary` + 7 hand-written modules; before
22:31:51–22:32:18, after 22:45:50–22:46:07, `Build completed successfully
(324 jobs).` for `Linksem LinksemAux HandwrittenTest main_link`). Verbatim:
`census3: 12074 constants in 201 modules (8 hygienic, 3 rounds, 3972 instance sites)`
before and after (12070 distinct). **596 declarations changed, all `def`,
596 explained, 0 not**; 5 in hand-written modules
(`Byte_sequence_wrapper.find_byte.go` and its `_f`/`_sunfold`/`_unsafe_rec`,
`Byte_sequence_wrapper.instBEqByte_sequence`, `Filesystem_wrapper.is_abs_path`),
0 in `_auxiliary`; 839 height-only hint changes; 3923 after-sites all core.
Pairs: `(Nat, instEq0Uint64_elf_types_native_uint_2)` 3010 / 409, `(String,
instEq0String)` 256 / 107, `(uint32, …_2)` 193 / 65, `(Nat, instEq0Nat_1)`
140 / 32, Char 90 / 12, `(uint64, …_2)` 51 / 19, Bool 51 / 24, Int 27 / 21,
UInt8 (comparator) 25 / 12, `cfa_register`/`cfa_offset`/`cfa_delta`/
`cfa_address`/`address_expr_fn_ref` 35 / 13, `sym`/`cabs_identifier` (String)
11 / 7, `cfa_sfoffset`/`integer_value_base` (Int) 6 / 3,
`sdt_unspecified_parameter` (Unit) 3 / 3, Int32 2 / 2, Int64 2 / 2, the nine
other `instEq0Uint*` chain members 2 / 1 each, `Ordering` (comparator, in
`instBEqByte_sequence`) 1 / 1.

The design note's estimates (about 903 and 736) were sums over rows in
which a declaration can appear more than once; the distinct counts are 675
and 596. `LinksemAux` (the model's executable assertions) and Cerberus's
`_auxiliary` modules built green on both sides: no asserted value moved.

### 6. Cerberus: the hand-written proofs

The unpatched after-build failed at exactly one place (verbatim):

```
error: generated/CerbCtypeMeasure.lean:342:2: 'show' tactic failed, pattern
  (match defaultCompare n1 n2 with
      | LemOrdering.EQ => true
      | x => false) =
      true ↔
    n1 = n2
is not definitionally equal to target
  Lem_Basic_classes.isEqual n1 n2 = true ↔ n1 = n2
```

`natEq0_iff` now reads `show (n1 == n2) = true ↔ n1 = n2; exact beq_iff_eq`
(its docstring updated); `symEq_iff` (`:351`) re-elaborates unchanged and
keeps using it. The patch is
[`2026-10-03_beq-lattice-cerberus-repin.patch`](2026-10-03_beq-lattice-cerberus-repin.patch);
`git apply --check` passes against both the frozen `51a7402ce` and the
mainline head `d6c548847` (nothing applied — the Cerberus re-pin waits for
its `_Alignas` and union-twin slices). With it the library built green; no
other hand-written file broke (the 182 hand-written declarations whose
terms moved all compiled). Not run here, for the re-pin: the full battery
per `scripts/LADDER.md`/VALIDATION.md cache-disabled, `check_failure_reach.sh`
(the kernel closures of `defaultCompare`/`instBEqOfSetType` leave many
declarations; neither contains a failure site), the axiom gate.

linksem: the hand-written tree needs no change. The default `lake build`
of the scratch copy failed only in `driver/MainElf.lean:32:45: Unknown
identifier `usage_text`` (and `:44:45`) on BOTH LemLibs — the primary's
driver is ahead of the frozen `f54d119` model, a frozen-input skew, not
this slice — so the after-build targeted `Linksem LinksemAux HandwrittenTest
main_link`.

### 7. TODO 45 retest (`automatic` on `n - 1` under `lem_if`)

Reproducer `let rec cnt (n : nat) : nat = if n = 0 then 0 else 1 + cnt (n - 1)`
with `declare {lean} termination_argument cnt = automatic`, generated by the
changed `lem` (`def cnt (n : Nat) : Nat := lem_if n == 0 then 0 else 1 + cnt
(n - 1)`) and compiled against the changed LemLib — still fails (verbatim):

```
error: Test_todo45.lean:17:4: fail to show termination for
  cnt
…
n : Nat
h✝ : ¬(n == 0) = true
⊢ n - 1 < n
```

Plain Lean 4.32.2 with core's `BEq` and no LemLib gives the same failure
(`T1`), so the default `decreasing_tactic` does not use the hypothesis even
when `==` is core's. What the slice changes: the same module with
`decreasing_by all_goals simp_all; omega` appended now builds (`Build
completed successfully (34 jobs).`), where the record's item 7 measured
`simp_all`/`omega` failing on the bridge. NOT closed: the remaining fix is a
design choice — an emitted `decreasing_by` forces well-founded recursion on
every `automatic` declaration (Cerberus's four list recursions, linksem's
`unzip3`), so it is for the operator; TODO item 45 carries the options,
DESIGN's row states the measured limit. No regression test was added.

### 8. cerberus-sl re-pin note (draft; read-only analysis at `12d247c`, no build)

Nine hand-written lemmas spell out the bridge and break or stop matching
(each becomes a core lemma):

| Site | Today | Replacement |
|---|---|---|
| `CerberusIris/Env.lean:30` `lemNatBeq_iff` | statement names `@instBEqOfEq0 Nat Lem_Num.instEq0Nat_1`; proof `show (match defaultCompare a b …)` — BREAKS | restate as `(a == b) = true ↔ a = b`, proof `beq_iff_eq` |
| `Env.lean:38` `lemNatBeq_eq_decide` | statement names the bridge; proof via `lemNatBeq_iff` | restate as `(a == b) = decide (a = b) := rfl` (uses: `Env.lean:59`, `EvalSubst.lean:47,64`, `SubstE.lean:34`) |
| `Lang.lean:177` `lem_nat_beq_iff` | `change (match setElemCompare …)` — BREAKS | `beq_iff_eq` (uses: `Env.lean:523`, `RoundCtrl.lean:1716`, `SelectBridge.lean:120,125`, `RulesS.lean:2266-2340`) |
| `EvalArms.lean:1597` `lem_int_beq_iff` | same shape — BREAKS | `beq_iff_eq` (uses: `EvalArms.lean:1686`, `HeapModelAlloc.lean:65`, `HeapModelKill.lean:59,66,108`, `HeapPtrEq.lean:127`, `Memory/Carrier.lean:223`, `PtrEqModel.lean:87`, `PureEvalS.lean:650,652,717`) |
| `Repr.lean:30` `int_beq_refl` | `show (match defaultCompare x x …)` — BREAKS | `beq_self_eq_true` (uses: `Repr.lean:209,831`, `HeapModelKill.lean:30,115`, `Memory/Carrier.lean:245`, `Memory/Transitions.lean:56,61`, `Memory/Unspecified.lean:36`, `PtrEqModel.lean:68`, `CerberusSL/IdiomsCall.lean:1664`, `InterfaceS.lean:1720,1761`) |
| `Repr.lean:411` `lem_nat_beq_self` | statement names the bridge; `change` — BREAKS | `beq_self_eq_true` (uses: `Repr.lean:418,419,422`, `Memory/Unspecified.lean:59,61`, `CerberusSL/StdLibEq.lean:290,708`) |
| `Call.lean:182` (inside `call_proc_eq`) | `change (match setElemCompare params.length params.length …)` — BREAKS | `beq_self_eq_true _` or `simp` |
| `CerberusSL/StdLibEq.lean:33` `lem_nat_beq_self` | re-export whose statement names the bridge | restate with `==` |
| `CerberusSL/RulesS.lean:2266` `lem_nat_beq_iff` | re-export, statement already `==` | unchanged (follows `Lang`) |

60 grep hits for the six lemma names outside `.lake`/`.cerberus-ws`/the quoted
corpus (definitions, re-exports, comments and uses together; the note's "about
64" was at `6edb0c4`). Under the new LemLib the two statements that name the
bridge still typecheck (`bridge_nat_is_core` is `rfl`) but no longer match the
generated `==` syntactically, so `rw`/`simp only` with them would stop firing:
restate them. Two `simp only [… beq_iff_eq]` calls were inert on the bridge
and will fire: `Recon/Admit.lean:742` (`simp only [runOK, Bool.and_eq_true,
beq_iff_eq] at this`, after which `obtain ⟨hl, hlen⟩ := this` and the `match
lp, hlen` see `… = …` instead of `(… == …) = true`) and `Recon/Arena.lean:393`
(`simp only [d11Call, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]`, then
`rcases h2 with …`); `Env.lean:26` `digest_compare_eq` uses the same simp set
and is to be re-checked. `Repr.lean:831` already hedges both forms.
Unaffected: the `fmapAddBy defaultCompare …` terms in `DriverLoop.lean`,
`RunBuild.lean` (comparator values, not `==`). The 762/55/3 `decide` closers
are on concrete facts. A full cerberus-sl build follows its re-pin.

### 9. Docs

Lattice note: the 2026-10-03 addendum (core's 500 row, the 450/400 rows,
the undocumented tie, deliberate tie 1 retired, the specificity rule, the
extended invariant and probe). DESIGN.md: "Instance priorities come from one
table" and the `termination_argument … = automatic` row; the manual
chapter's two matching paragraphs. TODO.md: 46 closed, 45 re-measured,
line references re-derived. RECORDS.md: this section and the design note
indexed.

### Gates (verbatim tails)

LemLib, `cd lean-lib && capped lake build`: `Build completed successfully (39 jobs).`
(the `#print axioms` lines of §4 are in the same log; the four pre-existing
unused-variable warnings only).

`scripts/ce make nonlean-regress`:
```
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
```

`scripts/ce env UPSTREAM_LEM=… LINKSEM=… CERBERUS=… make upstream-drift DRIFT_OUT=<empty dir>`
(same clients as packages A and C):
```
upstream-drift: upstream 3802cb0, fork lean-backend-v0.1.0-alpha.1-57-g8666b7f-dirty; clients compared: linksem cerberus
upstream-drift: 944 upstream files; 198 differ (list: …/beq/drift/differences.txt)
     26 backends/tex_all
     11 lib/coq
      7 lib/hol
     26 lib/html
      1 lib/ident.stdout
      7 lib/isa
     26 lib/lem
      7 lib/ocaml
     84 lib/tex
      3 lib/tex_all
library code files (OCaml/HOL/Isabelle/Coq):
  comments/whitespace only  lib/coq/lem_basic_classes_auxiliary.v
  [… 32 such rows, no code row]
make: *** [Makefile:60: upstream-drift] Error 1
```
(`cerberus-ocaml` and `linksem-ocaml` absent from the per-directory counts,
i.e. byte-identical; the non-zero exit is the script's report of the fork's
accepted non-code differences, as in every previous record.)

`scripts/ce make -C tests/comprehensive lean` (tail, verbatim):
```
test_version: OK (untagged, exact annotated tag, dirty tag, post-tag, archive fallback)
  OK: missing lean_constants refused; intact library generates
test_failure_admission: OK (registered probe with compiler failure is red, not XFAIL)
  OK: test_wide_patterns.lem generated in 2 s
  OK: refused: cannot create the output directory Makefile/sub: Makefile/sub: Not a directory
=== Generation: 73 passed, 0 failed, 0 skipped ===
  OK: equation form for f and len2, match form for g
Build completed successfully (208 jobs).
  [lean-compile: 773 PASS lines, no error; lean-panic, lean-untaken-failure, single-evaluation, supply, reader, fuel legs: every OK line as in the package C run]
  [lean-negative: 115 probes "OK (rejected as declared)"; lean-invariance: 10 witnesses "artifacts byte-identical across ocaml/hol/isa/coq"]
parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
=== No sorry/admit/axiom/native_decide in fuel_measure proofs modules (gate) ===
  OK: 11 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
=== No fuel numerals in LemLib or generated code (gate) ===
  OK: 325 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
suite exit 0
```

(Bracketed lines are derived summaries of blocks of identical OK lines;
every other line is verbatim. Run twice — 22:49–22:58 and, after the two
probe-comment edits of §3, 22:58–23:06 on the final sources — with
identical verdicts; the 15 lines containing "error" are the 14 parity
probes' "ocaml: failed as expected" lines and the negative-probes banner.
The "FAIL:" lines the parity runner prints inside the registered XFAIL
probes are its own reporting of the pinned Lean side.)

`make` leaves the tree clean apart from the intended changes (`git status`
at commit time: the eleven modified files and the patch file listed under
"Files"; the suite's `tests/comprehensive/invariance/_out/` is removed by
the phase that creates it).

### Files

`src/lean_backend.ml` (the priority table, the two bridge sites),
`lean-lib/LemLib/Basic_classes.lean`, `lean-lib/LemLib/Map.lean` (regenerated),
`lean-lib/LemLibTheorems.lean` (namespace `BeqLattice`),
`tests/comprehensive/lean-test/TestInstancePriorityCheck.lean` (legs 5, 6; the
leg-4 comment's bridge priority), `tests/comprehensive/test_instance_priority.lem`
(the RG2 comment's bridge priority),
`doc/notes/2026-08-22_arc14-instance-priority-lattice.md` (addendum),
`doc/lean-backend/DESIGN.md`, `TODO.md`, `RECORDS.md`, `doc/manual/backend_lean.md`,
`doc/lean-backend/2026-10-03_beq-lattice-cerberus-repin.patch`, this section.

### Provenance

[USER 2026-10-03]: the two rulings quoted at the top. [AGENT] (this worker):
every measurement, the three-row constant table, the theorem statements and
the decision to spell the old instance terms out, the probe legs, the census
instrument and its explanation criterion, the Cerberus patch, the cerberus-sl
table, the TODO 45 disposition and this record.

## Orchestrator verification of the BEq-lattice slice (2026-10-03)

The orchestrator re-ran the gates independently on `e87056f`, from the same
frozen inputs:
```
arc make exit 0   [tree clean after make]
cerb: 0 differing files / linksem: 0 differing files   [generated text vs 5dfcd25's lem]
lemlib exit 0  (Build completed successfully (39 jobs).)
=== Generation: 73 passed, 0 failed, 0 skipped ===
Build completed successfully (208 jobs).
parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
upstream-drift: 944 upstream files; 198 differ   [library code rows all comments/whitespace only; cerberus-ocaml / linksem-ocaml absent]
```
Direct probes against the new LemLib:
- `#synth BEq Nat` and `#synth BEq String` both give `instBEqOfDecidableEq`.
- The operator's `example (a b : Nat) (h : (a == b) = true) : a = b := by simpa using h` compiles.
- `#print axioms` on `BeqLattice.nat_old_eq_new`, `string_old_eq_new` and `bitVec_old_eq_new` gives `[propext, Classical.choice, Quot.sound]`; on `ordering_old_eq_new` it gives `[propext]`.
- With `pp.explicit`, `nat_old_eq_new` states
  `@BEq.beq Nat (@instBEqOfSetType Nat (@instSetTypeOfOrd Nat instOrdNat)) a b = @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) a b`.
  So it relates the old bridge instance to core's, and is not a vacuous `x = x`.
- The orchestrator did not re-run the declaration census (675 Cerberus / 596
  linksem changes, all explained). It is the pre-merge audit's to
  re-derive.

## Pre-merge audit (2026-10-04)

[USER 2026-10-03] asked for a fresh Fable audit over the full range. Auditor: Claude Fable 5.1,
fresh, on `5dfcd25..653ea3f`. Verdict: **merge after fixes**, all
documentation; no BLOCKER, no MAJOR. Notes and probes are in scratch,
`.tmp/audit-hardening/`.

What the auditor re-derived independently:
- **Gates:** green on every one.
- **Lattice census:** Cerberus 675 changed / 675 explained / 0 unexplained;
  linksem 596 / 596 / 0.
- **Plants:** `TestInstancePriorityCheck` fails exactly the nine leg-5 lines
  against base LemLib.
- **Cerberus patch:** applies to `51a7402ce` and `d6c548847`, and the
  library builds green with it.
- **Package C deletions:** zero hits in all consumers and in both
  regenerated trees.
- **Parser conflicts:** unchanged, and the same as upstream.
- **Package A plants:** each reproduces on base `lem`.

Findings and fixes (this commit):
- **MINOR-1.** DESIGN, TODO 47 and the manual said the renamed type variable
  is digit-suffixed (`{t1 : Type}`). The code primes it, as the record says:
  `{t' : Type}` (`Test_tyvar_collision.lean:52`). Corrected at all three
  sites.
- **MINOR-2.** TODO 45 still said "awaits the operator" after the ruling, and
  DESIGN's `automatic` row and the manual posed the question as open. Both now
  cite the [USER 2026-10-03] ruling to leave it open.
- **MINOR-3.** The 127-field admission is a runtime bound only. A variant
  constructor with 127 fields and derived comparisons exceeds Lean's
  elaboration recursion depth (`maximum recursion depth has been reached`).
  127-field structures, 120-field constructors, and 127-field constructors
  under `skip_instances` build. Now stated in DESIGN; the variant bound is
  TODO 49(a).
- **MINOR-4.** `Fin n` also switches winner (from the map-key comparator
  bridge to `instBEqOfDecidableEq`) and has no per-type theorem. It is covered
  by the generic `BeqLattice.mapKeyBridge_eq_core`; the auditor's `example`
  compiled. No consumer site is at `Fin`. "A kernel theorem for every type
  whose winner switched" in §4 is to be read with this generic coverage.
- **MINOR-5.** The type-variable rename does not collect constructors that
  appear only in patterns, and does not rename inside instance methods. Both
  are loud at the Lean build. DESIGN now names the two exclusions; TODO
  49(b).
- **NITs**, registered:
  - TODO 50: a type named like its own parameter; type variables named like
    reserved binders.
  - TODO 51: deeply nested types are slow in Lem's typechecker on every
    target, which makes the depth-50 refusal unreachable in practice.
