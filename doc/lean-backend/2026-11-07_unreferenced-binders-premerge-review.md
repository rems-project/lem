# Pre-merge review: `fix/unreferenced-binders` (TODO item 54, lem-lean half)

Date 2026-11-07. Reviewer [AGENT], independent of the worker and the orchestrator. Under review: branch
`fix/unreferenced-binders`, tip `5362006`, base mainline `mdd/lean-backend` `b154377` (three commits: M1
`4a2a72e`, M2 `2d9b36f`, M3 `5362006`); the charter
[2026-11-07_worker-charter-unreferenced-binders.md](2026-11-07_worker-charter-unreferenced-binders.md), the
record [2026-11-07_unreferenced-binders-record.md](2026-11-07_unreferenced-binders-record.md) and the consumer
note [2026-11-07_consumer-note-cerberus-unreferenced-binders.md](2026-11-07_consumer-note-cerberus-unreferenced-binders.md).
Reviewed against the container doc's working practices, the operator's rule that warnings are fixed rather
than suppressed, and this repository's README/DESIGN/TODO/RECORDS. The consumer (cerberus-lean, mainline
`1e5f2cbca`) was read only. Every count below is derived unless quoted.

## 1. What I ran (all from the worktree; the suite and LemLib were not rebuilt by me — the orchestrator's re-run
was in flight and is quoted in §4)

- The cerberus Lean tree regenerated with the branch's `./lem` (`Lem lean-backend-v0.1.0-alpha.1-84-g5362006`)
  from the primary checkout's `frontend/` (clean at `1e5f2cbca`) with the Makefile's exact `lean-prelude-src`
  flags and source list (86 sources) into scratch, then the recipe's `sed`; compared token-wise against
  `lean_frontend/generated/` and joined, module by module and line by line, with the warnings Lake stored in
  `lean_frontend/.lake/build/lib/lean/<Module>.trace` (`log` entries). Last lines: `172`, `lem.log identical`,
  `lean gen rc=0`.
- The cerberus OCaml tree regenerated the same way (the `prelude-src` flags, the four `sed`s) and byte-compared:
  `files new=86 ref=86`, `diff rc=0 (0 = byte-identical)`, `ocaml lem.log identical`.
- LemLib regenerated into scratch with the branch's `./lem` (the `library/Makefile` `lean-libs` command without
  `-only_changed_output`) and compared with the committed `lean-lib/LemLib/*.lean`: no differing file.
- Generation probes through `./lem -lean` (one file per shape, §3) and Lean 4.35.0 probes through
  `CERB_MEM_MAX=32G capped lake env lean` from `lean-lib/` (the linter's shapes; the mutual-block
  `termination_by` rule).
- The checker's plants P1–P3 on scratch copies of the generated `Test_unreferenced_binders.lean`, and the
  negative plant `lake build WarningPlant` under the cap.

## 2. Findings

### F1 (P1, blocking): a lem variable already spelled `_name` is emitted as `__name`; this is the whole 689-vs-676 gap

`binder_underscore` (`src/lean_backend.ml`) prefixes `_` to every unreferenced binder without checking whether
the source name already starts with one. Cerberus's lem sources use the OCaml convention `_name` for variables
they do not use, so the new backend turns them into `__name`. Measured on the regenerated cerberus tree (the
join of §1): 13 sites, exactly the record's unexplained excess:

    double-underscore sites: [('Annot', 505, '_loc1'), ('Annot', 505, '_loc2'), ('Annot', 517, '_loc1'), ('Annot', 517, '_loc2'), ('Cabs_to_ail_effect', 1632, '_ident'), ('Cabs_to_ail_effect', 1688, '_linkage'), ('Cabs_to_ail_effect', 1714, '_scope'), ('Cabs_to_ail_effect', 1714, '_linkage'), ('Cmm_csem', 1613, '_name'), ('Cmm_csem', 1616, '_name'), ('Cmm_csem', 1636, '_name'), ('Cmm_csem', 1637, '_name'), ('Translation', 5134, '_ty')]

(the lem origin, e.g. `frontend/concurrency/cmm_csem.lem:640`: `One (_name,setgen) -> …`; the new text,
`Annot.lean:499`: `| some (Identifier __loc1 "cerb"), Identifier __loc2 "magic" =>`). The full join:

    modules 172: binder renames 601 (41 mods), double-underscore 13, inhabited 75 (10 mods), termination_by removed 147 (29 mods), unclassified 0
    warnings: unreferenced 676 (44 mods), inert termination_by 147 (172 mods)
    renames without warning: []

i.e. 601 + 75 = 676: every warned binder is renamed and every rename other than the 13 matches a warning (the
75 `x<n>` warnings are the Inhabited change); the record's 614 = 601 + 13. The same defect is in the suite's own
tree: `Test_target_reps.lean:55: | (MkMyPair a1 __b) => a1`, `Test_functions.lean:111: | ((x : Nat) :: __xs) => x`,
`Test_misc.lean:91: | x :: __rest => x` (lem: `test_target_reps.lem:44`, `test_functions.lem:49`,
`test_misc.lem:88`), and my probe reproduces it: `def already_us (__x : Nat) (y : Nat) : Nat := y`,
`| some __v => 0`. Lean 4.35.0 accepts `__x` silently (probe `l1`), which is why no gate caught it.

Why blocking rather than should-fix: (a) the record's §4.2 and §9.1 explain the gap as "a shape the linter does
not report", which the tree does not bear out, and the consumer note's §1 says the 614 are "the source name
kept under the underscore", which is false for 13 of them; (b) the backend's own stated rule (`_err`, never a
bare `_`, so the name stays greppable) is violated — `__name` is not the lem's `_name`; (c) landing it ships 13
gratuitous hunks into the cerberus re-pin and cleaning them up afterwards costs a second two-repo pin dance.
The fix is small: `binder_underscore` returns `None` when the stripped name begins with `_` (a probe line in
`test_unreferenced_binders.lem`, e.g. `let keep_us (_x : nat) (y : nat) : nat = y` pinned as
`def keep_us (_x : Nat) (_y : Nat)`), then the counts re-derived: 601 binders, 75 Inhabited, 147 clauses in
the record §4.2, the consumer note §1/§3, TODO row 54 and the RECORDS row (all currently say 689/614), and
§9.1's explanation replaced.

### F2 (P2, should fix before the merge): the re-pin recipe omits the `rev` pinned in `lean_frontend/lakefile.toml`

Cerberus's `lean_frontend/lakefile.toml:95-99` requires LemLib with `rev = "e6d8db5680962f49060257d6c2bcb13c284b910f"`;
step 3 of the consumer note says only `lake update LemLib` in the three manifest packages. With the `rev`
pinned in the lakefile, `lake update` cannot move the manifest past it; the lakefile's `rev` (the container
doc's "Lake rev", the first of its five pin invariants) must be edited to the merged commit first, and the
`lake update` runs need `scripts/ce` (the `deps/gitconfig` redirect; otherwise Lake tries GitHub and fails
without network) and `capped`. The other two packages (`speclab`, `tests/mem-scale-probes/micro`) carry no
`rev` in their lakefiles; their manifests do (all three at `e6d8db5…`, verified). The fork-drift gate would
catch the omission loudly, but the note's purpose is a recipe that does not stumble.

### F3 (P3, note or small fix): the kept-name sets apply to every binding form inside a definition, not only to its parameters

`with_binder_scope` adds `St.keep_binders` (the structural parameter), the `reader_seed` parameters, the
hoisted tail binders and the sentinel's identifiers for EVERY pattern rendered while the definition renders,
nested arms and lambdas included. Two probes, each leaving a warning Lean reports (`l8` 20:93, `l9` 21:73 in
my Lean probe file), which under `-DwarningAsError=true` is a build failure with no remedy but renaming the lem
variable:

    | some tag => (fz_lemFuel lemFuel) 7 (n - 1)          -- a fuel'd def with sentinel `fuelExhausted tag`; the inner arm's `tag` is unreferenced
    | _ :: l2 => (fun (l : List Nat) => 1) ([] : List Nat) + slen l2   -- `declare {lean} structural val slen`; the nested lambda's `l` is unreferenced

No cerberus site hits this today (the join shows no warning left unmatched), so it is not a re-pin risk; but
the record's §9.2 names only the `_lem*` guard as a standing-warning hole, and the DESIGN paragraph says
"never" for names the clause names, which this over-approximation extends past its reason. Either narrow the
kept sets to the definition's parameter rendering (`funcl_aux`'s `fun_pattern_list` sites) or list the hole
in §9 with the two shapes.

### F4 (P3): the suite's count reconciliation is wrong, not merely unresolved

Record §4.1: 78 binders + 8 Inhabited = 86 against 87 warnings. Three of the 78 are the double-underscores of
F1 (no warning behind them), so the honest arithmetic is 75 + 8 = 83 fixes against 87 warnings, four
unaccounted. The gate (zero warnings under the flag, the orchestrator's re-run) is the signal, but §4.1 should
state the corrected numbers and either reconcile from the base log or say plainly that it did not.

### F5 (P3): "both of the fork's Lean packages" — the repository has five lakefiles

`lean-lib`, `tests/comprehensive/lean-test`, `tests/backends/lean-test`, `examples/cpp`,
`examples/ppcmem-model`. Only the first two carry `-DwarningAsError=true`. README's "a `lake build` that
completes is at zero warnings" and DESIGN's "both of the fork's Lean packages" should name the two and say the
other three are outside the rule (`tests/backends` red per TODO 56; the examples historical).

### F6 (P3, for the re-pin slice): "classify every hunk" must compare tokens, not lines

A `_` makes a binder one character longer, and the width-100 layout re-wraps: 15 of the cerberus hunks at line
level are re-flows (e.g. `Cabs_to_ail:6494`, `Translation:697-698`, the Inhabited blocks of
`Translation_aux:353-375`), token-identical apart from the three shapes. The consumer note's step 6 ("any
other hunk is a finding") should say so, or the re-pin slice will file re-flows as findings.

### F7 (P3): documentation length

The manual bullet (`doc/manual/backend_lean.md:46`) is a 90-word paragraph duplicating DESIGN; a sentence and
a pointer would do. DESIGN, README, RECORDS and the TODO row are otherwise short and current (counts aside,
F1); no log entries were added to the working-practices docs.

## 3. What the tree bears out (checked, no finding)

- **The analysis is the typed AST's and sees the emitted references.** Shadowing (`def shadow_in (_x : Nat) :
  Nat := (fun (x : Nat) => x) 1`), a nested use through a local lambda, the `_y@((a, b))` alias, the per-clause
  equation names (`| (0 : Nat), (y : Nat) => y` / `| (n : Nat), (_y : Nat) => n`), the restricted quantifier
  (`setForAll (fun (_x : Nat) => true) s`), keyword-named parameters (`(_from1 : Nat) (_at1 : Nat)` — the lem
  renamer runs first), record patterns (compiled to projections, the unused field vanishes). The unrestricted
  quantifier (`Qb_var`, rendered outside the rule) is refused upstream (`Translation error: cannot generate
  code for unrestricted quantifier`), and `P_num_add` is desugared before rendering, so neither is a gap. The
  hoisted-tail worker keeps `acc` and `lemTail` (`| 0 => ((fun _ => acc) lemTail)`), the seed def keeps `av bv gv`
  (`def via_seed3 (x : Nat) : Nat := seed3 7 "ab" 9 x`), the obligation shells and `_zero` lemmas bind through
  `binder_of` and reference every binder in their statements. The 108 named-argument sites in cerberus's
  hand-written Lean target type parameters or hand-written lemmas, none of the three generated defs whose `a`/`m`
  parameters were renamed (`nd_mem`, `warns_if_no_active_ex`, `relation_plug`).
- **Lean's rule on mutual blocks is per strongly connected component, as recorded.** My probe: the clause on a
  member outside every cycle and on a member that only calls into the cycle both warn
  (`l_scc.lean:8:0: warning: unused `termination_by`, function is not recursive`, `11:0` idem); a cycle with
  the clause on one member only, and a cycle with clauses plus a clause-less caller (the emitter's shape), are
  silent. `lean_block_recursive` implements reachability from the def's callees back to itself; the callee
  lists name siblings as `<t>.beq_derived`/`.compare_derived`/`.lemSize` and helpers by their memoized names,
  consistent with the def names in the block. The 147 removed clauses match the 147 warnings per module.
- **The linter's shapes.** Partial defs, instance methods, `let` destructuring, `do` lines, string-literal
  arms and `y@` aliases all warn on 4.35.0 (my `l_shapes` probe), so the renamed forms were real warnings, and
  `__x` is accepted (F1's silence).
- **The derived `Inhabited` constant function** now binds `_`; 75 sites in 10 cerberus modules, each a former
  `x<n>` warning.
- **The OCaml output is untouched**: only `src/lean_backend.ml` changed under `src/`; the cerberus OCaml tree
  is byte-identical (86/86, `lem.log` identical); LemLib's committed generated files equal a fresh regeneration.
- **The flags bite and the plants are real.** `lake build WarningPlant` under the package's
  `-DwarningAsError=true`: `error: TestWarningPlant.lean:8:33: Variable name `y` is not explicitly referenced.`,
  `error: TestWarningPlant.lean:11:0: unused `termination_by`, function is not recursive`, `error: build
  failed`, exit 1. The checker's control passes (`OK: 18 binder lines as pinned; termination_by on 12 of 46
  definitions, exactly the 12 that recurse; none on the 8 that do not`); P1 `FAIL (U1): … lacks the line: def
  def_params (x : Nat) (_y : Nat) : Nat := x`; P2 `FAIL (T1): rec_t.beq_derived recurses but carries no
  termination_by clause`; P3 `FAIL (T1): nonrec_t.beq_derived does not recurse but carries a termination_by
  clause (inert: Lean warns)`. The pins are typed (exact lines, named definitions), the plant is not a default
  target, and the target's cost is one module's build.
- **Readability.** `_name` reads well and keeps the lem name searchable (F1 excepted); no collision with the
  `_x<n>` positional wildcards (they are rendered by `binder_of`, in other definitions) or the synthesized
  `_lem…` namespaces (guarded; `_lemFuel` is a def-name suffix, never a binder).
- **Process.** Three coherent commits with provenance tags; no commit on a mainline; nothing pushed; the
  cerberus pin unmoved; no operator words quoted; `git status` clean.

## 4. The gates I observed (the orchestrator's re-run, `.tmp/orch-gates.log`, not run by me)

    2520:Build completed successfully (216 jobs).
    2521:=== Unreferenced binders and the per-definition termination_by (TODO item 54) ===
    2522:  OK: 18 binder lines as pinned; termination_by on 12 of 46 definitions, exactly the 12 that recurse; none on the 8 that do not
    2523:  OK (keep-guard leg): names in the synthesized binder namespaces are kept; a plain unreferenced one is underscored
    2524:  OK (plant): both warning kinds are build errors under -DwarningAsError=true (lake exit 1)
    2935:parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
    lem gates rc=0

The two `warning:` lines in that log are make's own recipe-override notices (`Makefile:10`, `ocamlbuild.mk:20`),
not Lean.

## 5. Verdict

Not as-is. The mechanism is sound and complete for the forms I could reach, the SCC rule is Lean's, the OCaml
side is untouched and the gate flags are real; but F1 is a defect in the rule the slice defines, it is the
unexplained gap the record carries as open, and it reaches the consumer as 13 wrong hunks that a second pin
dance would have to undo. Land after: F1 fixed with its probe and the four documents' counts corrected
(601/75/147), F2's recipe step added, the suite re-gated (`make -C tests/comprehensive lean` and the LemLib
build under the flag, last lines quoted). F3–F7 may follow in the same fix round or be recorded as open in the
record's §9.

## Dispositions (worker [AGENT], 2026-11-07; the code fix is commit `c846d39`, the documents this commit)

- **F1 — fixed.** `binder_underscore` leaves a source name already starting with `_` as it is (`src/lean_backend.ml`,
  the guard before the synthesized-namespace check). Probes in `tests/comprehensive/test_unreferenced_binders.lem`:
  `keep_us (_x : nat) (y : nat) = y` → `def keep_us (_x : Nat) (y : Nat) : Nat := y`, `use_us (_x : nat) = _x + 1` →
  `def use_us (_x : Nat) : Nat := _x + 1`, `arm_us` → `| some _v => 0`; `check_unreferenced_binders.py` pins the three
  lines (U1) and adds U2, no identifier in the module's code starting `__` (plant: a `__v` edited into an arm fails
  U1 and U2); `TestUnreferencedBindersCheck.lean` pins `keep_us (_x := 1) (y := 2)` and `use_us (_x := 1)`. The
  cerberus measurement redone with the fixed binary and joined against the stored warnings by module, line and
  name: 601 renames + 75 Inhabited wildcards = 676, 147 clauses = 147, 0 double underscores, 0 unmatched either
  way (record §4.2). The counts corrected in the record (§1, §4.1, §4.2, §9.1), the consumer note (§1, §3), the
  TODO 54 row and the RECORDS row; §9.1's "a shape the linter does not report" withdrawn. LemLib regenerated and
  unchanged (no such name in the library); `make lean-libs` left `git status` clean.
- **F2 — fixed** in the consumer note's step 3: edit the `rev` of `lean_frontend/lakefile.toml`'s `[[require]]`
  block for `LemLib` to the merged commit first, then `scripts/ce capped lake update LemLib` from each of the three
  packages with a manifest (`lean_frontend/`, `lean_frontend/speclab/`, `tests/mem-scale-probes/micro/`; the latter
  two carry the pin only in their manifests), with the reason for `scripts/ce` (the `deps/gitconfig` redirect;
  Lake would try GitHub and fail offline) and `capped` stated.
- **F3 — narrowed, not recorded.** `with_binder_scope` takes `~params`; the kept names (the structural parameter,
  the seed parameters, the hoisted tail binders, the sentinel's identifiers) are added only at the three sites
  where a clause head's parameters render (`funcl_aux`'s two assembly sites, `render_equation`); every pattern
  inside a body is decided on the body alone. Why narrow: every text that names a kept name names a parameter,
  so the wider set protected nothing, and the hole it left had no remedy under `-DwarningAsError=true` but a lem
  rename; the change is three call sites. Both of the review's shapes are probes: `loop_arm` (a fuel'd def whose
  sentinel names `tag`, with a nested arm binder `tag` → `| some _tag =>`, the worker's own `tag` kept) and `slen`
  (`declare {lean} structural val`, a nested lambda binder `l` → `(fun (_l : List Nat) => 1)`, the clause
  `termination_by structural l` kept), pinned in the checker and the Check file and compiled at zero warnings.
  Record §2.1, §3 and §9.2 and DESIGN's paragraph say so; the `_lem…` guard is now the one remaining
  standing-warning shape.
- **F4 — restated honestly.** Record §4.1: 75 + 8 = 83 fixes against the 87 warnings of the 4.35 record, four
  unaccounted for; the three double underscores named (`Test_target_reps.lean:55`, `Test_functions.lean:111`,
  `Test_misc.lean:91`). Not reconciled from the base log: it is not available (the primary lem-lean checkout's
  stored traces predate the 4.35 move, 2026-09-05, with the older message text), and a base rebuild for a P3 count
  on a shared box was not made; the gate is the signal. Open in §9.1.
- **F5 — fixed.** README ("How you check it") and DESIGN name the two lakefiles that carry the flag
  (`lean-lib/lakefile.lean`, `tests/comprehensive/lean-test/lakefile.lean`) and say the other three are outside
  the rule and every gate: `tests/backends/lean-test` (red before its build, TODO item 56), `examples/cpp` and
  `examples/ppcmem-model` (historical). Not added there: none is a claim surface, and `tests/backends` cannot
  build at all today. Record §9.5.
- **F6 — fixed.** The record §4.2 and the consumer note's step 6 state the classification as token-level, say why
  (the width-100 layout re-wraps lines one character longer), give the re-wrapped hunk count (13 by the worker's
  heuristic, 15 by the reviewer's) and tell the re-pin slice to join each hunk's old and new lines and compare
  tokens before filing anything.
- **F7 — fixed.** The manual bullet is one sentence and a pointer to DESIGN's "What generated code looks like".

Re-gated after the code fix (record §7.3, verbatim): LemLib under the flag, the full comprehensive suite, the
cerberus OCaml byte-compare (86/86) and the Lean measurement.
