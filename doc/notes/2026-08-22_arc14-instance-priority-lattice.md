# The instance-priority lattice (arc-14 S2 B4, be:G1)

Date: 2026-08-22. Status: NORMATIVE — every generated or library
comparison/equality instance priority is assigned from this table; an
instance at an undocumented priority is a finding. Enforcement:
`tests/comprehensive/test_instance_priority.lem` (build-failing resolution
probe) + the emission comments in `src/lean_backend.ml` citing this note.

## The table

Lean priorities: `default` = 1000, `low` = 100; numerals are literal.
Higher wins; ties resolve newest-declaration-first (an ORDER accident —
every deliberate tie below is justified; adding a new tie is a finding).

| Slot | Priority | Who lives here |
|------|----------|----------------|
| model/override | 1000 (default) | lem `instance` declarations from the source model (e.g. symbol.lem's name-only `Eq0 identifier`); hand-written override files (e.g. cerberus CerbStepInstances); LemLib's concrete instances for base types; the generic `[Eq0 a] : BEq a` bridge (see "deliberate ties"; the COMPARATOR-derived bridges live in the 500 row below — RG3: each bridge appears at exactly one priority) |
| derived BEq/Ord | 1000 (default) | the backend's derived/`deriving`-bridged **BEq/Ord** instances — MUST stay at default: below the default-priority `[Eq0 a] : BEq a` bridge they would be shadowed and the bridge would complete through `isEqual := x == y`, i.e. through THEMSELVES or a fallback (the pre-arc-10 failwithI race) |
| **auto trio + comparator bridges** | **500** | the backend's auto **SetType/Eq0/Ord0** trio (deriving-bridge and comparison-derived) — BELOW every model/override instance (they win by PRIORITY, not order — the sem:S2 fix), ABOVE every generic default and fallback. ALSO (re-mark R3): the class emitter's comparator-derived **BEq** bridges (`[SetType a] : BEq a`, `[MapKeyType a] : BEq a`) — a comparator can be COARSER than a type's own equality, so the isEqual bridge/derived BEq (1000) must beat them by priority (this was the third default-priority tie, now DE-TIED) |
| generic defaults | 100 (low) | `Basic_classes`: `[BEq a] : Eq0 a`, `[Ord a] : SetType a`, `[Ord0 a] : OrdMaxMin a`; LemLib's low-priority Sum right-inhabitant; residual (failwithI-bodied) trios/instances for underivable types |
| open-tyvar fallback | 50 | the unconstrained fallbacks for parameterized types (reached only when the bounded instance's `[BEq tv]`/`[Ord tv]` bounds cannot be synthesized; failwithI bodies — loud) |

## Deliberate ties (each with its justification)

(The third default tie the arc-14 re-mark found — the comparator-derived
BEq bridge vs the isEqual bridge, both formerly 1000 — is DE-TIED: the
comparator bridge now sits at 500, see the table.)

1. **derived BEq/Ord (1000) vs the generic `[Eq0 a] : BEq a` bridge
   (1000).** Newest-first: the derived instance (declared in the
   generated module, after Basic_classes) wins. Deliberate: the bridge
   exists for types whose ONLY equality is a model Eq0; lowering the
   bridge would break those, raising the derived instances is a no-op
   (they are already default). The residual order-reliance is confined
   to this pair and probed (probe leg 2).
2. **hand-written override files vs generated real instances (both
   1000).** Newest-first: the override file imports the generated module,
   so it is newer and wins — the documented override mechanism
   (cerberus CerbStepInstances/CerbFunMapInstances pattern). Deliberate:
   overrides exist precisely to win; a priority above default
   (e.g. 2000) is the escape hatch if an import-order accident is ever
   observed (none known).

## The invariant

> For every type with both an auto trio and a model/override instance of
> the same class, the model/override instance wins resolution — BY
> PRIORITY (1000 > 500), independent of declaration order. For every
> type with an auto trio and no model instance, the auto trio wins over
> the generic defaults/fallbacks (500 > 100 > 50).

## The probe

RG2 leg (re-mark): `prio_coarse` (coarse model SetType beside derived
structural BEq) pins that `==` resolves to the DERIVED BEq, not the
comparator bridge. Plant note (measured 2026-08-22): reverting the
bridge to default priority did NOT flip the guard — at the restored tie
the derived instance still wins by newest-declaration order (the bridge
in Basic_classes necessarily predates every derived instance), so the
de-tie converts that ORDER argument into a PRIORITY argument rather
than changing today's winner; the probe pins the intended winner under
both regimes.

`tests/comprehensive/test_instance_priority.lem` declares a type with derived
instances AND its own `instance (Eq …)` with distinguishable semantics
(first-field-only equality), then asserts through lem `=` that the MODEL
instance decided. If the auto trio ever wins the race again, the assert
fails at Lean build time (the comprehensive suite's assert compilation),
failing `make lean`. A second assert pins the no-model-instance case
(auto trio semantics, not a fallback panic).

## History

Pre-B4, the auto trio was emitted at default priority and the model's
own instance won by ORDER only ("equal priority resolves
newest-declaration-first") — the be:G1 finding: a semantic accident with
a runtime-failwithI (or silently-wrong-comparison) failure mode. The
sem:S2 sibling (cerberus generated Symbol.lean: location-sensitive auto
Eq0 vs name-only model Eq0 for `identifier`) is the concrete instance of
the hazard; B4 makes the intended winner win by construction.

## Addendum 2026-10-03: the `BEq` bridges below core (the BEq-lattice slice)

Ruling [USER 2026-10-03]: option (a), 450/400 (the recommended one), landing as
its own slice after A and C. Design pass:
`doc/lean-backend/2026-10-03_beq-instance-lattice-design.md`; the slice's
measurements and gates: `doc/lean-backend/2026-10-03_backend-hardening-record.md`,
"BEq-lattice slice". Everything below that is not the ruling is [AGENT].

**What the table above missed (measured against LemLib at `5dfcd25`/`8666b7f`,
Lean 4.32.2).** Core's `[DecidableEq a] : BEq a` (`instBEqOfDecidableEq`,
`Init/Prelude.lean`) is declared at priority **500**, not the default 1000.
So the generic `[Eq0 a] : BEq a` bridge at 1000 beat core by priority at
every base type (`#synth BEq Nat ⟶ @instBEqOfEq0 Nat Lem_Num.instEq0Nat_1`),
and the comparator bridges at 500 TIED with core — an undocumented tie, won
by LemLib as the newer declaration (`#synth BEq UInt64 ⟶
Lem_Map.instBEqOfMapKeyType …`). `==` at Nat therefore meant
`match defaultCompare a b with | .EQ => true | _ => false` through `Ord Nat`,
three instances deep, with no `LawfulBEq` and none of core's simp set.

**The rows now.** Higher wins; the relations of the original table all hold
except the two marked.

| Slot | Priority | Who lives here |
|------|----------|----------------|
| model/override, derived BEq/Ord | 1000 | unchanged (the `[Eq0 a] : BEq a` bridge has LEFT this row) |
| core `BEq` | 500 | `instBEqOfDecidableEq` — core's structural equality at Nat, Int, String, Char, Bool, Unit, the fixed-width `IntN`/`UIntN`/`ISize`/`USize`, `BitVec n`; NOT LemLib's to set, listed so the table is complete. Lean 4.35.0 (2026-10-21): at `Int` and the fixed-width types core's `Std.LinearOrderPackage` instances (`….toBEq`, above 500) win instead; still core's, `LawfulBEq` found (`Std.LawfulBEqOrd.lawfulBEq`); the bridges below are unaffected |
| auto trio | 500 | the backend's automatic SetType/Eq0/Ord0 trio, unchanged (`lean_instance_auto_priority`); the comparator BEq bridges have LEFT this row |
| **Eq0 bridge** | **450** | `[Eq0 a] : BEq a` (`lean_instance_eq0_bridge_priority`): below core, so a base type's `==` is core's; above the comparator bridges, so polymorphic `[Eq0 a] [SetType a]` code and a model-only type still get the finer `isEqual` route |
| **comparator bridges** | **400** | `[SetType a] : BEq a`, `[MapKeyType a] : BEq a` (`lean_instance_comparator_bridge_priority`): a comparator can be coarser than the type's equality, so every other `BEq` source beats them by priority |
| generic defaults | 100 | unchanged |

**Deliberate tie 1 is retired.** It read "derived BEq/Ord (1000) vs the
generic `[Eq0 a] : BEq a` bridge (1000), newest-first". Two corrections:
the bridge is now at 450, so there is no tie; and the derived instance never
won by declaration order — at equal priority a SPECIFIC instance (a derived
`BEq identifier`, core's `List.instBEq`) beats a STAR instance
(`[Eq0 a] : BEq a`) by discrimination-tree specificity whatever the order
(design note §2.3, measured). The plant note under "The probe" above
("reverting the bridge to default priority did NOT flip the guard") is the
same fact. Deliberate tie 2 (override files vs generated instances) stands.

**The invariant, extended.** For every base type with a core `DecidableEq`,
`==` is core's instance (500 > 450 > 400); for every type whose only
equality is a model `Eq0`, `==` is the Eq0 bridge (450 > 400 > 100); where
both an `Eq0` and a comparator dictionary are in scope and no core instance
applies, the Eq0 route wins (450 > 400). Values did not move: for every
switched type the old instance term equals the new one by a kernel theorem
(`lean-lib/LemLibTheorems.lean`, namespace `BeqLattice`).

**The probe, extended.** `tests/comprehensive/lean-test/TestInstancePriorityCheck.lean`
legs 5 and 6: `#synth BEq Nat/String/UInt64` must print
`instBEqOfDecidableEq`, `LawfulBEq` must be found at those types, the
operator's example `(a == b) = true → a = b` by `simpa` and
`(a == b) = decide (a = b)` by `rfl` must compile; a model-only type still
resolves to `instBEqOfEq0`, and polymorphic `[Eq0 a] [SetType a]` code to the
Eq0 bridge. Plant-tested: against the old priorities every leg-5 line fails
(verbatim errors in the hardening record).
