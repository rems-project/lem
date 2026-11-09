# Lean backend quality review — 2026-08-31

Provenance: professor-class review commissioned [USER 2026-08-31] ahead of
the effect-retirement + fuel-budget arc (a quick quality review of lem-lean
as a backend, folded into the arc). Review lens = the four project aims as
set by the operator [USER], paraphrased: (1) minimal blast radius for non-Lean
lem users, (2) obviously right output for Lean, (3) a clean and
understandable design, (4) built to be reviewed by the upstream lem team and
eventually upstreamed as
a lem feature." Reviewer: independent agent on branch `review/backend-quality`
@ 95ac6a5 vs `master` @ 3802cb0. Report reproduced verbatim below from the
reviewer's final message; committed by the orchestrator [AGENT] as the record.

Method: full read of the fork delta (`git diff master...HEAD -- src/` =
~6,090 lines, chiefly `src/lean_backend.ml` at 5,381 lines), full read of
`lean_backend.ml`, fresh `make` of the fork lem plus a scratch build of
upstream `master`, constructed reproducers run through both binaries, a
9-target master-vs-fork sha256 output sweep over two corpora, a full
`tests/comprehensive` Lean run, and a dedicated LemLib.lean review with
ocaml-lib mirroring.

## MAJOR

**M1. Seven new bare keywords are globally reserved — parser regression for
ALL lem users on ALL targets.** `src/lexer.mll:134-140` adds `fuel`,
`reader`, `effectful`, `ground_rep`, `reader_seed`, `skip_instances`,
`extra_import` to `kw_table` as hard keywords, with no identifier-production
escape in `src/parser.mly`. Evidence (verbatim): fork on `let fuel = (1:nat)`
→ `Syntax error` at line 1, character 4 (the identifier); master parses past
it (fails only on the probe's unrelated lib setup); the sweep reproduced the
same on an `-ocaml` run with pervasives (master: exit 0, emits
`let fuel:int= ((1:int))`; fork: syntax error). All seven words fail
identically. `fuel` and `reader` are entirely plausible identifiers in
semantics code — this is exactly aim-1 blast radius, and the first thing
upstream would reject. Remedy: make the new tokens usable as ordinary
identifiers (add them to the `x`/identifier nonterminal like a contextual
keyword, or accept them only in the `Declare ...` productions);
alternatively rename to collision-improbable compounds (upstream precedent:
`termination_argument`, `pattern_match`). Price **M**.

**M2. `integerDiv`'s Lean mapping is Euclidean division; the OCaml oracle
truncates toward zero.** `library/num.lem:1403,1406` maps lem `integer`
division to Lean `infix /` = `Int.ediv`, while OCaml uses zarith `Z.div`
(truncation). `(-7)/2` = −3 (OCaml) vs −4 (Lean). Live generated sites:
`cerberus-lean/lean_frontend/generated/Defacto_memory_aux.lean:150,166-193`
(`n / (2 : Int)` in bitwise decomposition), masked today only by unproven
operand nonnegativity. `integerMod` happens to match (`emod` ≡ `Z.erem`),
and the `num_extra` trio in `lean-lib/LemLib.lean:828-830` is correctly
mirrored — this one mapping is the outlier. Mirror-OCaml doctrine: defect as
such. Remedy: map `integerDiv` to `Int.tdiv` (and audit the
`NumIntegerDivision Int` instance at `lean-lib/LemLib/Num.lean:561-563`);
price **S**.

**M3. Non-ASCII char literals emit invalid Lean.** `src/lean_backend.ml:3487-3491`
renders `L_char` via OCaml `Char.escaped`, which uses decimal escapes.
Reproduced: `let c1 = #'\200'` → generated `def c1 : Char := '\200'` → Lean:
`error: invalid escape sequence` (verified against the toolchain). Loud, not
silent — but it is wrong output on legal lem input. Remedy: emit
`'\xHH'`/`\uHHHH` escapes for non-printable/non-ASCII; price **S**.
(Adjacent: `lean_string_escape` at `lean_backend.ml:101-113` passes bytes
0x80–0xFF through raw — lem's own lexer rejects non-UTF-8 strings, so this
is currently unreachable, but the pairing is fragile.)

**M4 (latent, differential-trust class). `setChoose` diverges from
`Pset.choose` undocumented.** `lean-lib/LemLib.lean:399-402` returns
newest-inserted head; OCaml `ocaml-lib/pset.ml:297,358` returns
comparator-minimum. Within lem's declared nondeterminism, but a live
order-observable consumer exists (`generated/Core_linking.lean:89`
`topo_order` — linked-definition emission order), and unlike the documented
set-iteration divergence (`LemLib.lean:303-305`) it carries no in-code
divergence note. Remedy: either mirror min-elt or add the divergence note +
a differential pin; price **S**.

## minor

**m1. The `-lem` identity echo of `extra_import` does not round-trip.**
`src/backend.ml` `Decl_extra_import` case uses `core (str ...)` (quote-char
rendering) instead of the backtick form. Reproduced:
`` declare {lean} extra_import `Foo` `` echoes as
`declare {lean} extra_import "Foo"`, which the fork's own parser then
rejects (`Syntax error` at the quote). This is precisely the historical
"declare-echo" regression class. Fuel/ground_rep echo the backtick form
correctly. Remedy: emit `` `Foo` ``; price **S**.

**m2. No in-repo regression net for non-Lean targets — the sha-sweep is
still luck.** Confirmed structurally: `tests/comprehensive/Makefile` is
Lean-only (`all: lean`), `tests/backends` `leantests` is generation-only,
there is no CI. The review's own sweep found all 9 non-Lean targets
**byte-identical** master-vs-fork over the 28-file library corpus and 20
backend tests — so shared-path edits are currently benign — but nothing in
the repo would catch the next regression. Remedy: a `make nonlean-regress`
target hashing ocaml/hol/isa/coq/lem/ident library output against committed
golden hashes; price **S/M**.

**m3. Un-gated shared-path edits (latent blast radius, empirically benign
today).** Four edits alter shared code for all targets rather than being
`Target_lean`-gated: (a) `src/target_binding.ml:61-78` —
`search_module_suffix` now falls back to global `e_env` when a module isn't
in `local_env`, which can change chosen suffixes/error behavior for any
target; (b) `src/typed_ast_syntax.ml:1193-1199` — `add_def_aux_entities` now
emits class paths + method consts into `used_entities` for all targets
(feeds `rename_defs_target` and avoid-sets at `src/main.ml:301-304`);
(c) `src/output.ml:470` — `to_rope`'s block-format path decodes UTF-8 where
upstream decoded latin1 (an unflagged fix; changes bytes wherever non-ASCII
flows through isa/hol block formatting); (d) `src/target_trans.ml:~460` —
`add_avoid_type` now silently returns `ns` on `None` where upstream raised
(fail-open conversion). All byte-identical on the sweep corpora, but each is
an upstream-review argument waiting to happen. Remedy: gate (a),(b) on
Target_lean or split them out as separately-argued upstream fixes; restore
the raise in (d); price **S** each.

**m4. Mutable global hooks on the shared path.**
`Backend_common.on_cr_simple_applied` (`src/backend_common.ml:385-391`) is a
process-global `ref` callback installed at every `lean_defs` entry
(`lean_backend.ml:5217`) and **never uninstalled**; the `is_lib` computation
in `function_application_to_output` (`backend_common.ml:540-556`) runs for
every CR_simple application on **every** target even when the callback is a
no-op. Together with `St.current_module_name` (pre-call side channel from
`process_file.ml`), these are the registered be:S15 residuals — but upstream
will reject a global ref callback in `Backend_common`. Remedy: thread
through the `Backend.Make`/`A` sig (the be:G3 pattern already named
in-code); price **M**.

**m5. `doc/manual/backend_lean.md` (the upstream-facing manual) is severely
stale.** It documents the deleted DAEMON axiom (lines 40-42, 78),
sorry-based stub instances (37, 80), and claims lemmata/theorems generate
`by decide` proofs (25) — the backend actually drops them as comments
(`lean_backend.ml:1640-1647`). `fuel`, `reader`, `reader_seed`, `ground_rep`
are absent from the manual entirely (fuel/reader/reader_seed are in
`doc/lean-backend/DESIGN.md`; `ground_rep` is documented nowhere except
lem.ott and code). The grammar itself IS properly in `language/lem.ott`
(+ registered ott-regeneration residual). Remedy: rewrite the manual chapter
to current behavior; price **S**.

**m6. The "sorry-emission paths are gone" header claim
(`lean_backend.ml:84`) is contradicted by the `Backend "sorry"`
pass-through** (`lean_backend.ml:2992-2998`), which actively special-cases
and type-ascribes a target_rep spelled `sorry` — and one live
`(sorry : String)` sits in the consumer's built cone
(`generated/Cmm_op.lean:292`, imported by Driver). Under the fork's own
fail-closed doctrine this is either a declared boundary (then register it
and fix the header) or a hole (then error on it). Price **S**.
(Consumer-side: `generated/CerbFunMapInstances.lean:6-8` describes the
pre-arc-10 sorry-fallback that no longer exists — stale doc there too.)

**m7. Tuple-destructuring `Let_def` duplicates the RHS per bound name.**
Reproduced: `let (aa, bb) = (true, false)` emits two defs each re-evaluating
the full RHS (`lean_backend.ml:2078-2126`). Pure code: only duplicate work;
an `effectful` RHS would run its effect once per binding where OCaml runs it
once — a silent-divergence shape. Remedy: emit one private def +
projections, or fail closed on effectful RHS in destructuring lets; price
**S**.

**m8. `process_file.ml` Lean branch shells out
`ignore (Sys.command "mkdir -p ...")`** — fail-open (ignored exit),
non-portable, and un-OCaml (use `Unix.mkdir`/rec helper, check result).
Price **S**.

**m9. Library-name entanglement inside a "generic" backend.** Hardcoded:
`compare_method_names = ["setElemCompare"; "mapKeyCompare"]`
(`lean_backend.ml:1805`), `lean_default_instance_extra_constraints`
"Eq0"/"SetType" (1505-1510), `lean_builtin_inhabited_entries`
"either"/"vector" (347-351), `lean_cmp_shape` "list"/"maybe"/"either" heads
(954-967), `lean_global_names = ["max";"min";"compare"]` (1837), and the
library-module test as a `{coq}`-rename proxy (`backend_common.ml:252-273`,
honestly documented as a registered residual). Individually defensible (the
lem library is fixed); collectively the largest upstreamability friction
after M1. Price **M** (mostly documentation + the already-registered
source-path library test).

**m10. LemLib residuals affecting trust posture** (from the dedicated
review): live `partial def`s in the shipped library
(`LemLib/Set_extra.lean:60`, `LemLib/List_extra.lean:58`, `natSqrtAux` at
`LemLib.lean:684`) escaping the fuel discipline; the never_extract/CSE
protection "verified against Lean 4.29" claim (`LemLib.lean:59`) never
re-verified on the deployed 4.32.2 — an unwritten per-toolchain-bump
obligation that the deletion arc dissolves; `int32Asr`/`int64Asr` positive
branch shifts the unnormalized value (`LemLib.lean:802-817`, unused by
cerberus); `setSigmaBy` ignores its comparator, `chooseAndSplit` drops
pivot-EQ elements off-invariant (386-410, unused); dead duplicates
`listGet?`/`listGet!` vs the wired `listGetOpt`/`listGetBang` (708-709 vs
836-837), verbatim-duplicate `lemStringFromNatHelper` (924-935).
Division-by-zero silently totalizes to 0 vs OCaml's raise — known sites
guard, but the class deserves one in-code note. Axiom inventory is clean and
honest: exactly one axiom (`runEffectful`, declared temporal boundary),
three `unsafe`+`@[implemented_by]` impls, two `opaque`s, no `sorry`, no
`native_decide`.

## notes

- `lean_defs`'s prop-equality **App** case (`lean_backend.ml:2908-2913`)
  doesn't parenthesize operands while the **Infix** case does (3277-3281,
  with an explicit chained-`=` comment) — inconsistent; a chained equality
  in an indreln antecedent through the App path could misparse (loudly).
- Clause-grouping is implemented twice with different keys: pre-pass groups
  by cref (`lean_backend.ml:1129-1138`), emission by name string
  (2140-2148) — a divergence trap for the coming arc.
- `lemDefaultFuel` is not in the reserved-name contract (2371-2401): a user
  def of that name would silently rebind the wrappers' fuel budget. Cheap to
  add to the check.
- The multi-clause "equation compiler" render path (2257-2293) may be dead
  post-`Patterns.compile_def` (`is_lean_pat_direct` rejects toplevel
  `P_const`, `src/patterns.ml:2115-2140`) — verify with a probe and either
  keep a test on it or delete it.
- Verified NON-bugs (so the arc doesn't re-litigate them): unparenthesized
  `match if b then l1 else l2 with` is valid Lean (probe-verified);
  `t_to_src_t` delimits nested type applications
  (`src/typed_ast.ml:2552-2578`), so `pat_typ` argument parenthesization is
  sound; `ast_target_to_int` renumbering only feeds equality comparison
  (`typed_ast.ml:353-355`) — benign; the fuel worker's `Nat.succ lemFuel`
  shadowing is intentional and correct; the fuel/reader/seed
  unsupported-combination guards (2302-2421) are comprehensive and
  fail-closed with 13 negative probes backing them.
- Generated-output cosmetics: pervasive double spaces
  (`def  f   (b  : Bool)`) from ws-skip + explicit-space concatenation, and
  `(({ ... } : T))` double parens — upstream reviewers will read generated
  samples; worth one cleanup pass.
- The fork's `library/*.lem` (bare `declare lean target_rep`) no longer
  parses under upstream lem (verbatim: `Expected substitution target in
  {hol; isabelle; ocaml; coq; tex; html}, given lean`) — expected, but it
  means library edits must ship in the same upstream patch series as the
  target itself.

## tests/comprehensive — Lean-target coverage

`make lean` = 4 phases: generation (40 .lem files, **40/40 OK**, empty
expected-failures list), compile+assert (`lake build` executes 586 `assert`s
as elaboration-time `#eval` checks — all green, a false assert fails the
build), one compiled-binary panic pin (failwithI raise, both legs OK), and
13/13 negative probes each required to fail **with the declared error
fragment**. Run verbatim result: exit 0; `=== Generation: 40 passed, 0
failed, 0 skipped ===`, `Build completed successfully (116 jobs)`, all
probes `OK (rejected as declared)`. Note: the Makefile's `lake build` is not
capped-wrapped internally (the review ran it under `capped`).

**Top 3 coverage gaps:** (1) `ground_rep` has no dedicated test and no
negative probe — only the library's single `fromJust` use exercises it
indirectly; (2) `effectful` is one declaration deep with no compiled-code
test that the CSE/extraction armor actually works (and the documented
instance-method limitation is untested) — critical given the coming
deletion arc must prove behavioral equivalence; (3) essentially nothing runs
as compiled native code (586 asserts all elaborator-evaluated; only the
panic pin is a real binary), so interpreter/compiler divergences — exactly
the class the panic pin caught once — are otherwise invisible. (Bonus:
`lemma`/`theorem` asserts are silently dropped as comments — tests relying
on them assert nothing.)

## Advice for the coming arc (supply-threading + per-declaration fuel budgets)

**Fix first, before building:** (1) **M1** — the arc adds more declare
grammar; land the contextual-keyword fix first so new words (`supply`?)
don't compound the regression, and add the non-Lean regression net (m2) in
the same slice so grammar work is guarded structurally, not by sweep-luck.
(2) The clause-grouping duplication (notes) — supply-threading will need a
*third* traversal of def groups; unify grouping into one shared function
(cref-keyed) first or the three will drift. (3) m4 — do not add another
global `ref` for the supply; the arc should ride the `St` module discipline,
and ideally pays down `on_cr_simple_applied` into the `Backend.Make`
signature while touching that seam.

**Where the new features attach cleanly:** the fuel machinery is the right
chassis. Per-declaration fuel budgets are a small delta: the sentinel
already flows `declare {lean} fuel val f = ...` →
`const_descr.fuel_sentinel` (`typecheck.ml` Decl_fuel case) →
`St.fuel_emit`/`St.fuel_workers` → `funcl_aux` (`lean_backend.ml:2790-2806`)
and the wrapper (2497-2504); a budget is one more `Targetmap` field on
`const_descr` + replacing the hardcoded `lemDefaultFuel` at 2504 — and then
**add `lemDefaultFuel` and the budget binder to the reserved-name contract**
(2396-2400). Supply-threading should be modeled on the **reader-lifting**
pipeline, which is the best-engineered mechanism in the file (declare →
typecheck field → `lean_reader_prepass` fixpoint → `St.reader_lifted` →
injection at exactly two emission sites, 2940/3046, with the arity guard) —
but note the reader mechanism's stated restrictions (single reader for
seeds, no instance methods, no infix position, 3260-3267) all apply verbatim
to a supply, and a *stateful* supply is strictly harder than a *reader*: it
must thread out as well as in.

**From the LemLib deletion-readiness review:** the axiom cluster
(`LemLib.lean:31-60`) is self-contained and cleanly deletable, but (a) the
backend co-removal must include the wrap emission AND the
`exp_contains_effectful` attribute machinery (2090, 2230-2235, 2474) or
dead armor lingers; (b) the threaded supply must reproduce the OCaml
counter's *dynamic call sequence* (symbol numbers are observable via
printing and map ordering), including the one-shot draw in
`Core_run_aux.lean:395`; (c) scope trap: `CerberusFresh.digest`, `CerbTags`,
`CerbGlobal` etc. are pure-signature externs in the same hazard family that
do **not** thread like a counter — decide explicitly whether the arc's bar
is "axiom gone" or "no impure pure-signature constants"; (d) extend the
existing absence-gate to ban `runEffectful` reintroduction after deletion;
(e) fix **m7** (tuple-let duplication) before threading a supply through
`Let_def`, since a duplicated supply draw is a silent numbering fork.

**Overall verdict against the four aims:** (2) and the fail-closed
engineering are genuinely strong — the pre-pass/emission split, the
negative-probe suite, and the reserved-name contract are upstream-quality
work; (1) is violated once but seriously (M1); (3) is good-and-improving
(the St module) with the residuals honestly registered; (4)'s blockers are
M1, the stale manual (m5), the global hook (m4), and the library-name
entanglement (m9) — all bounded, none architectural.

---

## Erratum (2026-09-01, appended at L2 per charter §8.5): M2 WITHDRAWN — VERIFIED-NO-DEFECT

[AGENT] (L2 worker, executing the registered rider; adjudication:
L0 item 5 + charter §8.5 @64dd6efeb, independently re-verified by the
L0 fresh-eyes audit — see `2026-08-31_arc-audit-log.md`.)

M2 above asserted lem `integer` division maps to Euclidean `Int.ediv`
on Lean while the OCaml oracle truncates via zarith `Z.div`. **This is
FALSE at the actual call target.** The chain is `integerDiv` →
`Nat_big_num.div` (`library/num.lem:1403` — the OCaml declare;
`:1405` is the COQ `Z.div` line, itself a plausible source of the
confusion) → `Big_int_Z.div_big_int` (zarith's num-compat layer) —
**Euclidean**, agreeing with Lean's `Int.ediv` at every signed corner
(measured verbatim on both targets, including compiled binaries;
`integerMod` likewise). Applying M2's remedy (`Int.tdiv`) would have
INTRODUCED the divergence it warned about. Parity is PINNED on both
targets: `tests/comprehensive/test_integer_div.lem` + the compiled
suite phase `lean-div-parity`. Record: L0 fix-first record §"Item 5"
(`2026-08-31_L0-fix-first-record.md`); correction of record until this
erratum: the effect-retirement charter §8.5 (cerberus-lean
`lean_frontend/docs/2026-08-31_effect-retirement-design.md`).

Auditor-recommended residue, kept: raw truncating `Z.div` DOES exist
in cerberus's hand-written OCaml memory-model seams — four sites:
`memory/vip/impl_mem.ml:1021` (the `IntDiv` arithmetic op) and `:718`
(pointer-difference division), `memory/concrete/impl_mem.ml:1393`
(prefix-offset naming) and `:1967` (pointer-difference division on a
possibly-negative address difference) — so the mirror obligation lands
THERE when/where those seams are ported, not in this library's
`integer` mapping. The ported concrete-model mirror already handles
the class correctly: cerberus-lean `CerbMem.lean:985` defines
`integerDiv_t := Int.tdiv` (docstring citing the truncating `Z.div`),
used at `:1013` (the `IntDiv` op path, explicit zero guard) and
`:1868` (`diffPtrval`); the vip model is unported and its obligation
attaches at porting time.
