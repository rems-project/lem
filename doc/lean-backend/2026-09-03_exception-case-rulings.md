# Exception-case rulings — X1 and X3/N4 (2026-09-03)

Resolves `2026-09-03_parity-fix-record.md` §4 ("EXCEPTION-CASE arguments
for the operator (not decided here)") for the two cases still open after
X2 and X4 were fixed as class-(c) generation-time refusals (the
`LemUnsupported.` marker hook, `3c88f0d`). Docs-only; no code changes.

## 1. The rule and the ruling

The standing rule [USER 2026-09-03]: zero behavioural discrepancies
between the OCaml reference and Lean; every such discrepancy is by
definition a bug unless an extraordinarily compelling case against that
is made now, and all legacy permission is revoked as of that date.
Accepted exception classes: (a)
failure-path message text; (b) resource limits (Lean must not fail where
OCaml succeeds); (c) missing features refused at generation time.

The operator asked whether the lem-lean cases are bugs in upstream
lem. The orchestrator's [AGENT] answer, put to the operator
2026-09-03 (verbatim excerpts):

> Not bugs in the sense of "upstream got it wrong" — and the check
> reframes both in a way that fits your rule better than "exception"
> does.
>
> 63-bit `nat`/`int`: a documented design compromise in upstream lem,
> not a bug. […] lem's semantics — as realized by its HOL, Isabelle and
> Coq backends — is unbounded, and the OCaml backend is the deviant, by
> explicit upstream choice. The Lean target (`nat → Nat`) sits on the
> theorem-prover side. Under "follow the LEM semantics," this isn't an
> exception to the rule; it's the rule applied […] The raising
> conversions we fixed are consistent with what OCaml itself does at the
> boundary. Nothing to file; at most a one-line note in the eventual lem
> submission that the Lean backend follows the prover-side reading.
>
> Polymorphic compare on closure-carrying values: an OCaml-backend
> representation artifact, worth an upstream note. Lem's mathematical
> semantics defines set equality; the OCaml backend represents sets as
> records carrying a comparator closure, so OCaml's structural
> `=`/`compare` raises `Invalid_argument "compare: functional value"` on
> any value containing one. Lean compares structurally and succeeds —
> again matching the prover-side semantics. […] it belongs in the lem
> submission bundle as a known-limitation report with the reproducer,
> not as a lem-lean action.
>
> So for the census I'd record both not as "exceptions" but as
> "OCaml-backend deviations from lem's own semantics; the Lean target
> follows lem (prover-side); parity is not required in the OCaml→Lean
> direction here".

[USER 2026-09-03] agreed with the lem framing — the framing above is the
ruling.

## 2. Disposition

Both cases are classified as **OCaml-backend deviations from lem's own
semantics; the Lean target follows lem (prover-side); parity is not
required in the OCaml→Lean direction here.** They are NOT exception
classes (a)–(c) and do not widen them.

### X3 / N4 — `nat`/`int` are 63-bit machine integers on the OCaml target

- lem's normative statement, `library/num.lem:104-111`, verbatim:

  > "nat" is the old type "num". It represents natural numbers.
  > These numbers might be bounded, however no checks of the boundedness
  > are provided. The theorem prover backends map nat to unbounded size
  > natural numbers. However, OCaml uses the type "int", which is bounded.
  > Using "int" allows using many functions like "List.length" without
  > wrappers. This leeds to nice readable code, but a slightly fuzzy
  > concept what "nat" represents. If you want to use unbounded natural
  > numbers, use "natural" instead.

- Lean `nat → Nat`, `int → Int` (unbounded) is the prover-side reading;
  the silent wrap of `+`/`*`/`abs` above 2^62 on OCaml (parity record N4,
  measured: `maxint+1 -> -4611686018427387904`) is the OCaml backend's
  documented compromise and is NOT mirrored.
- The checked conversions landed at `3c88f0d` (`natFromNatural`,
  `natFromNumeral`, `intFromInteger`, `intFromNumeral` fail loudly
  outside [-2^62, 2^62-1], where `Nat_big_num.to_int` raises
  `Failure "int_of_big_int"`) STAY [AGENT]: at that exact boundary the
  OCaml reference fails, so both targets fail (the rule's direction is
  preserved); this is the one place where the Lean target sides with the
  OCaml boundary rather than the prover reading, recorded here as a
  deliberate, revisitable choice — no lem semantics assigns a value there
  for the OCaml target, and a value ≥ 2^62 is unreachable in cerberus's
  model (its C arithmetic lives in `integer` = Z).
- Upstream: nothing to file. The lem submission carries a one-line note
  that the Lean backend follows the prover-side reading of `nat`/`int`.
- Tests: the conversion checks are pinned by the parity runner
  (`f_int_of_big_num`, both-fail); the arithmetic wrap has no runner row
  by design (a runner row would pin a known non-parity), the measurement
  is quoted in the parity record's N4 row.

  **Addendum 2026-09-04 (fuel-parameter arc, commit on branch
  `arc/fuel-parameter`) — the "conversion checks STAY" sentence above is
  SUPERSEDED.** [USER 2026-09-03]: OCaml limits hardcoded because of
  OCaml-level execution issues are forbidden as well; the logical
  semantics is what counts. The 63-bit checks in
  `lemNatFromNatural`/`lemIntFromInteger` (added at `3c88f0d`) were an
  OCaml-execution artifact, not lem's semantics: REMOVED; both
  conversions are the identity on Lean's unbounded `Nat`/`Int`, end to
  end (`natFromNumeral`/`intFromNumeral` were already literal
  pass-throughs). The parity row `f_int_of_big_num` is now a registered
  OCaml-target deviation in `tests/comprehensive/parity/expected_failures.txt`
  (entry class 2, citing this addendum): the runner requires it to fail
  parity (Lean succeeds where the OCaml reference raises) and reports it
  XFAIL. Other LemLib behaviours examined under the same principle
  (listed in `2026-09-04_fuel-parameter-record.md` §4 table and §9 D4): the `int32`/`int64`
  fixed-width WRAP is lem's declared semantics (stays); the loud failures
  that mirror OCaml *raises* (division by zero, `Z.sqrt` of a negative,
  `of_string` of an invalid literal, `Not_found`, `Invalid_argument
  "Array.sub"`) are failure-parity items under exception class (a), not
  limits (stay); the `Nat_big_num.to_int32/to_int64: Overflow` raise on
  `int32FromInteger`-style conversions is a candidate of the same kind as
  X3 (the prover-side reading is `word_of_int`, i.e. wrap) and is put to
  the operator in the record's decisions section, unchanged here.

  **D4 addendum 2026-09-04 (structural-declare slice, commit on branch
  `arc/structural-declare`) — the `int32FromInteger`-family Overflow
  raise: RULED, WRAP.** The fuel-parameter record §9 D4 found that lem's
  prover-side reps of `int32FromInteger`/`int32FromNatural`/
  `int32FromNumeral` and the `int64` trio are `word_of_int` (Isabelle) /
  `n2w` (HOL) — MODULAR (`library/num.lem:831-832`, `:1040-1041`,
  `:2378-2470`); the `Nat_big_num.to_int32/to_int64: Overflow` raise is
  the OCaml backend's, an OCaml-execution artifact of the X3 kind under
  [USER 2026-09-03] (the logical semantics is what counts); the
  record recommended that the Lean reps become the modular conversions.
  [USER 2026-09-04], adopting the orchestrator's recommendations
  (proceed with the merges as proposed, then work on this as
  suggested) — D4 = WRAP. Done: the Lean reps are `lemInt32OfInt`
  (`Int32.ofInt`) / `lemInt32OfNat` (`Int32.ofNat`) and the `Int64`
  pair; `lemInt32FromNumeral`/`lemInt64FromNumeral` are `Int32.ofNat`/
  `Int64.ofNat`; `lemInt32OfIntegerExact`, `lemInt32OfNaturalExact`,
  `lemInt64OfIntegerExact`, `lemInt64OfNaturalExact` are DELETED (no
  other user). Parity: `f_int32_overflow` is a registered OCaml-target
  deviation (`tests/comprehensive/parity/expected_failures.txt`, entry
  class 2, citing this addendum: the runner requires it to fail parity —
  Lean wraps where the OCaml reference raises — and reports XFAIL);
  `p_int_wrap` (the in-range and `Int32.of_int` wrapping rows) is
  unchanged and still byte-identical. This closes TODO row 11. The
  classification of the remaining LemLib behaviours in the paragraph
  above (failure parity for raises that are not limits) stands.

  **Addendum 2026-09-30 (branch `arc/linksem`): the arithmetic-wrap
  runner row now EXISTS.** [USER 2026-09-30] agreed on points 1-3 of the
  orchestrator's questions and approved proceeding. Question (2) was to keep
  the `p_word_bitwise_wide_mul` runner row, reversing this section's "the
  arithmetic wrap has no runner row by design". The row is
  `tests/comprehensive/parity/probes/p_word_bitwise_wide_mul.lem`, entry
  class `ruled` in `tests/comprehensive/parity/expected_failures.txt`: int/nat
  bitwise operations on operands built by multiplications that wrap at
  63 bits on OCaml. It was acceptable because, since 2026-09-30, a
  registered probe's Lean side is pinned exactly
  (`expected/<probe>.lean.out`), so the row pins the known difference
  instead of absorbing new ones. Question (1), under the same ruling,
  accepted LP4 (unbounded int/nat bitwise reps; OCaml wraps at 63 bits) and
  OM4 (mword width from the type; OCaml uses the runtime width) as
  registered OCaml-target deviations of this X3 class (`p_word_bitwise_wide`,
  `p_mword_width`, class `ruled`; record
  `2026-09-30_library-parity-coverage.md`).

### X1 — polymorphic compare on values containing a set or map

- OCaml `compare`/`=` on a `Pset`/`Pmap` value raises
  `Invalid_argument "compare: functional value"` (the record carries a
  comparator closure; `compare` on physically identical closures excepted);
  Lean's structural `BEq`/`Ord (Pset α)` instances compute. Lem's
  semantics defines set equality mathematically (`setEqual`, comparator-
  keyed on both targets); the raise is a representation artefact of the
  OCaml target.
- Code-side record: the in-code note at the instances,
  `lean-lib/LemLib.lean:741-748` (already in place; it states the OCaml
  behaviour and that lem's own set equality is the comparator-keyed
  `Pset.equal`). No change.
- Upstream: a known-limitation report with a reproducer goes into the lem
  submission bundle; whether upstream files it as a bug or documents it is
  theirs to decide. Not a lem-lean action.
- Tests: not probed (a probe needs a cerberus-shaped type carrying a set
  field and a structural `=` on it); the submission-bundle reproducer will
  be written when the bundle is assembled.

### X2 / X4 — closed before this ruling

Fixed at `3c88f0d` as class-(c) generation-time refusals (parity record
§3 rows X2, X4; `negative/neg_unsupported_*.lem`). The residual question
in X4 — whether `real`/`float64` should be SUPPORTED on Lean `Float`
instead of refused — was not put to the operator today and stays in
`TODO.md` as an open item.

## 3. Provenance

[USER 2026-09-03]: the rule (§1) and the ruling agreeing with the lem framing. [AGENT]
(orchestrator): the framing quoted in §1, the disposition wording of §2,
the decision to keep the conversion checks, the upstream-note plan.
[AGENT] (parity-fix worker, `3c88f0d`): the measurements quoted from the
parity record. Nothing was merged or pushed in this slice.

## 4. Addendum 2026-10-03 — X5: `min`/`max` default methods on the OCaml target

Found by the behavioural noodler of 2026-10-03 (`p_user_ord_instance`):
with a user `Ord` instance whose `<=` reverses the order and no
`OrdMaxMin` instance of its own, `min (T 1 0) (T 2 0)` is `T 1 0` on the
OCaml target and `T 2 0` on Lean; `<`, `compare`, `Sorting.sort`,
`isSorted`, `insert` and the set operations agree.

- Cause: `library/basic_classes.lem` defines `defaultMax = maxByLessEqual
  (<=)` and `defaultMin = minByLessEqual (<=)` — lem's semantics follows
  the instance — and gives them the OCaml representations
  ``declare ocaml target_rep function defaultMax = `max` `` /
  ``… defaultMin = `min` ``: Stdlib's structural `max`/`min`, correct only
  when the instance coincides with OCaml's structural order. HOL4, Isabelle,
  Coq and Lean use lem's definition (Lean emits `maxByLessEqual (fun x y =>
  not (tcmp x y == GT))`). Upstream report: `doc/upstream-tray/11-default-max-min-structural-on-ocaml.md`
  (LP1; the record `2026-09-30_library-parity-coverage.md` §2 had
  classified it as a question).
- Ruling: [USER 2026-10-03] register it as a deviation. The same
  class as X1 and X3: an OCaml-backend deviation from lem's own semantics;
  the Lean target follows lem; parity is not required in the OCaml→Lean
  direction. No OCaml representation is changed.
- Register: `tests/comprehensive/parity/probes/p_user_ord_minmax.lem`,
  class `ruled` in `parity/expected_failures.txt`; the OCaml pin
  `expected/p_user_ord_minmax.out` records the deviating reference output
  (`min: (1, 0)`, `max: (2, 0)`), the Lean pin
  `expected/p_user_ord_minmax.lean.out` lem's semantics (`min: (2, 0)`,
  `max: (1, 0)`); the explicit `maxByLessEqual (<=)`/`minByLessEqual (<=)`
  lines of the probe agree on both targets. DESIGN's deviation list carries
  the entry. Record: `2026-10-03_backend-hardening-record.md` item 10.
- Provenance: [USER 2026-10-03] the ruling; [AGENT] (backend-hardening
  worker) the probe, the register entry and this addendum.
