# Arc 3: totality-sweep mechanisms in the Lean backend

Companion to the consumer-side charter
(`cerberus-lean/lean_frontend/docs/2026-08-18_arc3-totality-sweep-charter.md`).
Four extensions, each probe-first in `tests/comprehensive/` (sections 12–14
plus the `negative/` lane).

## 1. fuel × reader composition (B1)

Previously fail-closed. Now: the worker's binder order is
`(lemFuel : Nat)` → reader binders → original arguments, so the point-free
wrapper `f := f_lemFuel lemDefaultFuel` has the reader-prefixed type and
lifted callers inject into the wrapper exactly as for any lifted def.
Worker self-calls re-inject the reader binders alongside the decremented
fuel. Probe: section 12 (applied caller + bare HOF reference).

## 2. fuel × mutual composition (B2)

Previously fail-closed. Now: a block-level fuel plan registers every
fuel'd def's worker before rendering, so self- AND cross-member calls
rewrite to `(worker lemFuel)` — every hop passes the decremented binder
and Lean sees mutual structural recursion on fuel. Rules, both enforced
fail-closed and message-asserted by the `negative/` lane:
- ALL-OR-NONE: every member of a fuel'd mutual block must carry its own
  `declare {lean} fuel val` (a non-fuel'd member would reset the fuel via
  the wrapper).
- fuel'd-mutual × reader-lifting stays unsupported.
Wrappers of a mutual block are emitted AFTER `end` — inside, they would
join the recursion set. The self/cross-call hooks fire only while a
fuel'd body is being rendered (`lean_fuel_emit` set), so non-fuel'd
siblings of mixed non-mutual blocks keep calling the wrapper.
Probe: section 13 (ping/pong with a non-structural edge).

## 3. Witness-based sentinels (`LemLib.fuelExhausted[With]`)

For fuel'd defs whose return type is pure (no error channel) and possibly
polymorphic. `opaque fuelExhaustedWith (msg : String) (witness : α) : α`
— the witness (any in-scope value of the return type, typically a worker
argument) discharges inhabitation LOCALLY: no `[Inhabited]` constraint
propagates into generated signatures, no generated-instance DAEMON
fallback enters theorem cones. Opaque ⇒ no equations ⇒ the fuel-exhausted
branch is not provably equal to anything (in particular NOT to the
witness); `@[implemented_by]` panic ⇒ honest-loud at runtime. The
message-less `fuelExhausted` exists because the backtick lexer excludes
double quotes. Probe: section 12b.

## 4. Acyclic de-mutualization

`let rec ... and ...` blocks whose call graph is a DAG (ignoring
self-loops) emit as SEQUENTIAL defs in stable topological order (Kahn);
`mutual` is reserved for genuine cycles. De-mutualized members get
per-member keywords: plain `def` when not self-recursive, `def` under
their own `termination_argument` declare, `partial def` otherwise.
Rationale: Lem sources use rec-and chains freely for non-mutual defs
(cerberus's subst/convert families are DAGs); keeping them mutual blocks
per-member termination handling and forces fuel onto defs that are not
even recursive. Probe: section 14 (dag family; per-member declare), with
section 13's cyclic pair as the stays-mutual regression check.

## Known limits (fail-closed or by-construction)

- fuel on multi-clause defs: unsupported (raise).
- fuel × reader_seed, fuel'd-mutual × reader: unsupported (raise).
- Pair-list recursion (e.g. Ecase's `List (pattern × expr)`) is beyond
  Lean 4.29's automatic derivation even after de-mutualization — attach
  fires but the decreasing goal cannot chain through the pair match.
  Consumer-side policy: such defs take fuel (consumer decision log D6).

## Post-audit notes (2026-08-18)

- In a DE-MUTUALIZED (acyclic) block where fuel'd A calls fuel'd B, A's
  body emits `(B_lemFuel lemFuel)` — the callee runs on the CALLER's
  remaining fuel, not its own default budget (the block-level worker plan
  covers the whole block). Sound (topo order scopes it; exhaustion is
  loud) and load-bearing for genuinely mutual blocks; recorded because it
  is observable at exhaustion.
- Negative lane extended with reader_seed×fuel; multi-clause×fuel and
  instance×fuel raises remain probe-less (recorded as thin coverage).
