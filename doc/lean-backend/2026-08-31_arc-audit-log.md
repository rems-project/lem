# Effect-retirement arc — lem-lean audit log

Committed by the orchestrator [AGENT] so the repo carries the audit
verdicts the arc's records cite (the full reports were delivered
agent-to-orchestrator; verdicts and load-bearing findings are recorded
here; the responding fix commits carry the per-finding detail).

## L0 fix-first slice audit (fresh-eyes, subject 582d901..4fd4d50)

VERDICT: **MERGE-SAFE** — L1 cleared to dispatch on the base.
- M2 adjudication: **REVIEW-WRONG-WORKER-RIGHT.** Independent re-derivation:
  lem's OCaml runtime chain (`library/num.lem:1403` → `Nat_big_num.div` →
  `Big_int_Z.div_big_int`, linked via findlib `lem` → `lem_zarith`) is
  Euclidean (probe: `Big_int_Z.div_big_int (-7,2) → -4` ≡ `Z.ediv`, ≠
  `Z.div → -3`); two-target compiled probe byte-identical at every signed
  corner. The quality review's `Z.div` claim traced to hand-written
  memory-model seams (`memory/vip/impl_mem.ml:1021`,
  `memory/concrete/impl_mem.ml:1393`) and the coq target_rep
  (`num.lem:1405`) — neither on lem's OCaml path.
- All eight items re-verified (own keyword probes ×3 targets; scratch-built
  parent compilers for the byte-identity claims, 82/82 and 3-site diffs
  confirmed; regression-net plant re-fired with hash rows matching the
  record verbatim; own plant against the setChoose pin fired). Record
  integrity: every quoted line reproduced.

## L1 features slice audit (fresh-eyes, subject 4fd4d50..a51615e)

VERDICT: **MERGE-SAFE-WITH-NOTES**, one MAJOR gating C1:
- **MAJOR-1**: supply transform's Infix branch threaded `&&`/`||` right
  operands strictly — draws hoisted above the short-circuit
  (`sc_and 10 false = (false, 11)`, correct `(false, 10)`); violates
  charter O1; maskable by id-canonicalized differentials. Fixed by
  4bff8b7 (branch-arm threading).
- minors 1-5 (duplicate supply/reader binder conflation; supply-on-defined-
  val; inert fuel budgets; two record corrections) — fixed by 4bff8b7.
- Positive: 16/16 guards located + probe-confirmed; own compiled
  draw-sequence witness matched hand-computed expectations (rfl-pinned);
  O7 structural claim verified by exhaustive emitter read; fuel opt-in
  verified by scratch-build (92/92 byte-identical); deviations 1-5
  adjudicated (dev-4 → the C1 Let_def-value cone-check obligation).

## L1 audit-response delta audit (fresh-eyes, subject 4bff8b7 alone)

VERDICT: **CLEAR-FOR-C1 (CLEAR-WITH-NOTES)** — no MAJOR; 39 own
kernel-pinned probes green (deep nesting, left-operand, right-assoc
chains, App-spine, `-->`, fuel composition); tree-diff zero-emission-change
claim independently reproduced; all new guards fired; record corrections
reproduce.
- **NOTE-1 (the registered L2 rider), verbatim substance:** the
  paren-split spine `((&&) a) (chk 4)` silently threads STRICTLY (draw
  fires on `a = false`: pinned `prefsc2 10 false = (false, 11)`) because
  `strip_app_exp` (`src/typed_ast_syntax.ml:803`) doesn't unwrap `Paren`,
  so the head lands in the general-head branch
  (`src/lean_backend.ml:3825`), bypassing both the shortcircuit leg and
  its fail-closed error. Verified **oracle-faithful**: OCaml is strict for
  exactly this eta-expanded shape (1 call at `a = false`) while the flat
  form short-circuits (0 calls) — lem-lean now matches case-for-case. But
  the match rests on lem's `Paren` node coinciding with OCaml's
  full-application detection — undocumented, unprobed, fragile under any
  future spine normalization. Rider: a probe pinning the strict behavior
  + an in-code note (L2).
- NOTE-2: the record's "fails closed otherwise" App-spine claim is
  overbroad (the paren-split fully-applied form is a third, silently
  strict, behavior-correct path) — record precision only.
- NOTE-3: fuel budget on a zero-arg value binding produces a vacuous-but-
  live wrapper (semantics preserved; doc-note at most).
