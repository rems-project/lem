# L2 deletion slice record — effect-retirement arc (lem-lean)

Worker record [AGENT] (L2 worker), 2026-09-01. Branch
`arc/effect-retirement`, base `af5df71`; slice commits `faa9fe4`
(deletion) + `7e56047` (riders) + this record. Governing docs: the
charter (cerberus-lean
`lean_frontend/docs/2026-08-31_effect-retirement-design.md`
@`64dd6efeb`) §7.1/§3.2/§8.1/§8.5; the audit log
`2026-08-31_arc-audit-log.md` (NOTE-1). Precondition (orchestrator-
stated): C1 complete and audited — the cerberus consumer @
`1b40098ed` has zero runEffectful occurrences in generated code and
zero `declare {lean} effectful` in its model; its pins point at
`af5df71` and bump to this head at C2.

## 1. Deletions (commit `faa9fe4`)

lean-lib:

- `LemLib.lean`: the `runEffectful` axiom, `runEffectful_impl`
  (unsafe), the `implemented_by`/`never_extract`/`noinline`
  attributes on both, and the scaffold commentary. A HISTORY note
  remains in place, per the charter's DAEMON precedent
  (`LemLib.lean:20-29`). LemLib now declares **zero axioms**
  (`grep -rnE '^\s*axiom ' lean-lib/ --include='*.lean'` → no hits).
  `supplySplit` stays. `lean-lib/README.md` front matter updated to
  the zero-axiom story.

src/lean_backend.ml (all Lean-target-only; the non-Lean emitters are
untouched, gated by nonlean-regress byte-identity):

- the call-site wrap emission: `is_effectful` classification and the
  `(runEffectful (fun () => ...))` thunk wrap in the App-Constant
  branch;
- the whole `exp_contains_effectful` attribute machinery:
  the predicate itself, `effectful_attr` on the three Let_def
  emission shapes (single-name, supply-threaded, and the m7
  `lemLetRhs_*` single-RHS def), `attr_for` on Fun_def groups and
  its carry onto fuel wrappers (the 4-tuple `(attr, kw, body,
  wrapper)` narrowed to 3);
- the now-unreachable transitional guards (dead armor, per the
  review's deletion-completeness item): the supply × effectful
  annotation-mix guard, the RC-mix effectful leg, and the
  effectful-head-with-supply-drawing-arguments guard in the supply
  transform;
- stale comments referencing the mechanism (Infix NOTE, m7 note,
  fuel-wrapper attr note) rewritten to present tense.

## 2. The refusal decision (RETAIN annotation + fail-closed refuse)

DECISION [AGENT] (orchestrator-prepared, executed here;
operator-overridable at the merge gates): the `effectful` ANNOTATION
— lexer word, grammar production, `Decl_effectful` AST/typecheck
plumbing, the `const_descr.effectful` field — is **retained**, and
its Lean-target handling is a FAIL-CLOSED refusal
(`lean_effectful_retired_check`, run at every pre-pass entry, firing
for every `{lean}`-effectful-marked constant even if unused):

> Lean backend: val NAME — 'declare {lean} effectful' is retired on
> the lean target; use supply lifting instead ('declare {lean}
> supply val', the deterministic state-passing transform). The
> library's effect-projection axiom and the call-site wrap were
> deleted by the effect-retirement arc (charter: cerberus-lean
> lean_frontend/docs/2026-08-31_effect-retirement-design.md
> @64dd6efeb, section 7.1)

Rationale (this deliberately supersedes charter §7.1's
grammar-deletion end state and its §7.3 P1 parse-error plant):

- grammar stability: the word stays available for other targets'
  potential use, and no grammar churn reaches the 9 non-Lean
  emitters (nonlean-regress stayed byte-identical with zero golden
  updates — the grammar-deletion route would have had to prove that
  separately);
- fail-closed doctrine: a refusal that NAMES the migration path is
  strictly louder and more instructive than a parse error;
- the negative probe (`neg_effectful_retired.lem`) documents the
  migration path forever, in the suite, with the declared-reason
  check (a wrong-reason rejection fails).

P1's intent (reintroduction is loudly impossible) is carried by the
refusal probe instead of a parse-error probe. **C2 note:** the C2
ratchet/plant designer should treat `neg_effectful_retired.lem` as
the P1 analog; the plant text in charter §7.3 ("lem must refuse
(parse error)") should be read as "lem must refuse (generation-time
refusal)".

## 3. Test conversions

- `test_target_reps.lem` Section 7 (the positive effectful wrap
  test: `get_counter`/`use_counter`) → replaced by a tombstone note
  + the negative probe `negative/neg_effectful_retired.lem`
  (EXPECT: `'declare {lean} effectful' is retired on the lean
  target`).
- `negative/neg_supply_mix.lem` (supply × effectful mix) deleted —
  the transitional guard it pinned is deleted; the refusal probe
  supersedes it (the refusal fires before any mix logic could).
  Negative probe count: **41 → 41** (−1 +1); supply×reader and
  supply×reader_seed mix probes remain.
- `test_tuple_let_once.lem` (the m7 single-evaluation pin — the one
  remaining test exercising the wrap) **converted, not deleted**:
  the pin is review-mandated (L0 m7) and its observable (RHS
  evaluation count via a hidden counter: (1,2) vs (1,4)) is
  independent of the supply machinery, so it stays as the
  non-supply leg of the m7 net. `TupleLetTick.lean` now hand-writes
  the pure-typed impure extern entirely in the test scaffold
  (`tickPair : Unit → Nat × Nat` = opaque + implemented_by unsafe
  impl + `never_extract` armour on both), and the .lem drops the
  effectful declare for a plain identifier-form target_rep. This
  models exactly the class of hand-written impure externs the
  retirement leaves to consumers' own armour. There is no other
  lem-side FreshIntTest analog (wrap-distinctness test) — census:
  the only effectful-exercising tests were the three above.

## 4. Riders (commit `7e56047`)

(a) **NOTE-1 paren-split strictness pin** (audit log NOTE-1,
    charter §3.2 rider i): `test_supply.lem` gains `chk` +
    `prefsc_paren a = ((&&) a) (chk 4)`; generated emission verified
    to route through the general-head branch (argument hoisted →
    strict). Four kernel `rfl` pins in `TestSupplyCheck.lean`,
    headline row `prefsc_paren 10 false = (false, 11)` (strict:
    draws despite `a = false`; contrast the flat-form
    `sc_and 10 false = (false, 10)` short-circuit row).
    **Plant-tested red-green**: flipping the pin to `(false, 10)`
    fails the TestSupplyCheck build; reverted, green. In-code notes
    added at the supply transform's general-head branch
    (`src/lean_backend.ml`) and at `strip_app_exp`
    (`src/typed_ast_syntax.ml`, comment-only) documenting the
    oracle-faithful coincidence and the re-adjudication duty on any
    future Paren normalization.

(b) **M2 erratum** (charter §8.5, rider ii): dated section appended
    to `2026-08-31_backend-quality-review.md` — VERIFIED-NO-DEFECT;
    the Euclidean chain (`num.lem:1403` → `Nat_big_num.div` →
    `Big_int_Z.div_big_int`); the four hand-written `Z.div` seams
    (vip `impl_mem.ml:1021`/`:718`, concrete
    `impl_mem.ml:1393`/`:1967`) with the `CerbMem.lean:985`
    `Int.tdiv` parity note.

(c) **Q1b-rescope notice** (R3.1, rider iii): dated section appended
    to `2026-08-31_effect-retirement-external-review.md`, addressed
    to the consumer: the §2 "one order-moved site" /
    escalation-clause / "behavior preserved (O2/O6)" statements are
    superseded per charter §3.6.1/O2/O6 and the C1 adjudication
    [USER 2026-09-01].

Optional item (3) of the brief (`check_renumber_only.py` hardening)
is cerberus-side (C2) and was NOT touched, per the brief.

## 5. Close-out battery (at the committed head, after `7e56047`)

Baseline (pre-slice, `af5df71` + root make): full suite exit 0
(verbatim harness echo: `exit=0`; the detailed baseline log was lost
to a sandbox-private /tmp — old counts below are from the file
census of `af5df71` and match the audit log / L1 record's recorded
47/47, 41/41). A second baseline attempt raced with the first edits
and was DISCARDED, not cited.

Close-out run (`make -C tests/comprehensive lean`, exit 0),
verbatim:

```
=== Generation: 47 passed, 0 failed, 0 skipped ===
  OK: test_cross_recup_base.lem + test_cross_recup_import.lem (joint)
  OK: test_cross_field_access.lem + test_cross_field_access_import.lem (joint)
=== Panic-path pin (failwithI raise at the L_undefined arm) ===
  OK (leg 1): panic prints the Incomplete Pattern message, then continues with default
  OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1
=== m7 single-evaluation pin (tuple-let RHS runs once) ===
  OK: draws: first=1 second=2
=== M2 integer division parity pin (compiled) ===
  OK: parity holds (Euclidean, both targets)
=== Supply draw-sequence pin (compiled) ===
  OK: compiled draw sequences hold
=== reader_consumer injection pin (compiled) ===
  OK: compiled consumer injection holds
=== Per-declaration fuel budget pin (compiled) ===
  OK: budgeted cut at 5; unannotated at the exact lemDefaultFuel boundary
  OK (rejected as declared): negative/neg_effectful_retired.lem
```

- Generation: **47/47 → 47/47** (no test files added/removed at top
  level; section 7 of test_target_reps converted in place).
- Negative probes: **41/41 → 41/41** (composition changed:
  −neg_supply_mix, +neg_effectful_retired; every row
  `OK (rejected as declared)`, derived count 41 confirmed by grep
  over the run log).
- Compiled phases: all green (panic ×2 legs, m7, div-parity,
  supply-draws, reader_consumer, fuel-budget).
- lean-invariance: all green, verbatim rows include
  `OK: inv_supply.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)`.
- nonlean-regress, verbatim:
  `nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)`
  — zero golden updates; the deletion is Lean-target-only.
- lean-lib: `lake build` — verbatim
  `Build completed successfully (35 jobs).`
- Rider pin plant: TestSupplyCheck red on the flipped pin
  (`error: Lean exited with code 1 ... - TestSupplyCheck`), green on
  revert.

## 6. Grep proof

`grep -rn runEffectful lean-lib/ src/` (excluding `src/_build`):

- **src: 0 occurrences** (the refusal message and its comment
  deliberately avoid the token).
- **lean-lib: 2 occurrences, both inside the charter-mandated
  HISTORY comment** (`LemLib.lean:32-33`), zero live declarations;
  `grep -rnE '^\s*axiom '` over lean-lib: **0 hits**.
- Test-tree comments (`neg_effectful_retired.lem`,
  `TupleLetTick.lean`, `test_target_reps.lem` tombstone) name the
  deleted mechanism descriptively; they are outside the stated
  lean-lib/src scope and outside the C2 ban surface (generated/,
  hand-written cerberus .lean, the LemLib copy).

**Flag for C2's ratchet designer** (raised, not silently absorbed):
charter §7.2's "grep-ban ... in the LemLib copy" and §7.1's "a
HISTORY note remains (DAEMON precedent)" are in tension if the ban
is implemented as a naive grep — the DAEMON precedent (HISTORY notes
name the deleted thing; the axiom census comment-strips) argues the
C2 ban leg must comment-strip too. Adjudicate there.

## 7. Slice state

- Commits: `faa9fe4` (deletion), `7e56047` (riders), + this record.
- NO merge, NO push, NO pin bumps (C2 bumps cerberus's opam/Lake
  pins to this head).
- Non-Lean output movement: NONE (byte-identical goldens, zero
  rebaselines).

---

## Addendum (audit response, appended same-day): F1 fix + plant re-execution, F2 name drift, C2 inputs

[AGENT] (L2 worker, responding to the L2 fresh audit's NOT-MERGE-SAFE
verdict; one audit-response commit.)

### F1 (MAJOR): the converted m7 pin was VACUOUS as shipped — fixed

The auditor demonstrated (compiled IR) that with `never_extract`/
`noinline` only on `tickPair`/`tickPairImpl`, the compiler extracts
the closed application `unsafeBaseIO tickPairIO` inside
`tickPairImpl` into a module-init cached constant
(`tickPairImpl___closed__0`): the action runs ONCE at init, both
projections read the cached pair, and the pin stays green even under
the reverted (duplicated-RHS) emitter. Root cause: closed-term
extraction reaches THROUGH outer attributes — the extracted closed
term mentions only `unsafeBaseIO` and `tickPairIO`, neither marked.

Fix (auditor-demonstrated, applied): `@[never_extract, noinline]` on
`tickIO` AND `tickPairIO` in `TupleLetTick.lean`; the false header
comment (which credited the outer attributes with preventing the
caching) replaced by an accurate armour-placement note stating WHY
the inner names need marking.

**Plant re-executed by this worker post-fix** (m7 emitter reverted
in-place in `src/lean_backend.ml` — `rhs_binding` forced to `None`
so multi-name lets duplicate their RHS per binding — root make,
regenerate, rebuild, run; then `git checkout`-restored, root make,
regenerate, rebuild, run). Verbatim:

RED (reverted emitter; generated `first_draw`/`second_draw` each
carry their own `TupleLetTick.tickPair ()` call — verified in the
regenerated Test_tuple_let_once.lean):

```
draws: first=1 second=4
single-evaluation FAILED: RHS did not run exactly once (got (1, 4), want (1, 2))
red-run exit: 1
```

GREEN (emitter restored):

```
draws: first=1 second=2
single-evaluation: OK
restored-run exit: 0
```

### F2 (doc note, no code change): rider probe name drift

The audit log's NOTE-1 rider text quotes the auditor's probe name
`prefsc2` (`prefsc2 10 false = (false, 11)`); the delivered probe is
named `prefsc_paren` (`prefsc_paren 10 false = (false, 11)`,
TestSupplyCheck.lean). Substance identical — same shape
`((&&) a) (chk 4)`, same pinned strict result.

### Recorded for the C2 brief (no action in this slice)

- The auditor's ratchet-leg proposal is accepted as C2 input —
  notably leg (3): pin the `@[implemented_by]`/`unsafe` population
  of the LemLib copy to the enumerated survivor pairs
  (`failwithIImpl`, `fuelExhaustedWithImpl`), because the zero-axiom
  census alone does not ban an axiom-free reintroduction of the
  effect projection via opaque + implemented_by + unsafeBaseIO.
- Hygiene (accepted, practiced in this addendum's runs): slice
  baseline/battery logs belong in repo-side or container-`.tmp`
  logs, never sandbox-private `/tmp`.

### Close-out (post-fix, at the audit-response commit's tree)

Full comprehensive suite exit 0 — verbatim:
`=== Generation: 47 passed, 0 failed, 0 skipped ===`; negatives
41/41 (`OK (rejected as declared)` row count 41); m7 phase verbatim
`OK: draws: first=1 second=2` / `single-evaluation: OK`; all other
phases green. nonlean-regress verbatim:
`nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)`.
Worktree clean after commit; `src/lean_backend.ml` byte-identical to
`7e56047` (the plant edit was ephemeral and restored from the
index).
