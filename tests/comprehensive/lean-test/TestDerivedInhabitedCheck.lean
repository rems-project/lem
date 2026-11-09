/- Arc-8 S1: hand-written checks for the DERIVED Inhabited instances
   emitted for tests/comprehensive/test_derived_inhabited.lem.
   Each `example ... := inferInstance` asserts that instance synthesis
   succeeds with EXACTLY the bounds the backend is specified to emit
   (design note doc/notes/2026-08-20_arc8-inhabited-threading-design.md
   rules 1-6): the binders written here are the only Inhabited facts in
   scope, so success means the derived instance demands no more than
   them. Uninhabited `Empty` instantiations additionally pin the
   UNCONDITIONAL cases. -/
import Test_derived_inhabited

/- 1. Two-constructor monadic shape: one instance per usable
   constructor — [Inhabited a] via ROk (default priority) AND
   [Inhabited e] via RErr (low priority). Both must fire. -/
example : Inhabited (res Nat String) := inferInstance
example {a e : Type} [Inhabited a] : Inhabited (res a e) := inferInstance
example {a e : Type} [Inhabited e] : Inhabited (res a e) := inferInstance
/- ... including with the OTHER side uninhabited. -/
example {a : Type} [Inhabited a] : Inhabited (res a Empty) := inferInstance
example {e : Type} [Inhabited e] : Inhabited (res Empty e) := inferInstance

/- 2. Mutual wrapper pair: node_ has an unconditional instance (NLeaf)
   plus a bounded one (NVal); the wrapper derives through the sibling. -/
example : Inhabited (node_ Empty) := inferInstance
example {b : Type} [Inhabited b] : Inhabited (node b) := inferInstance

/- 3. either field: bounded through LemLib's Sum inl/inr pair. -/
example {a : Type} [Inhabited a] : Inhabited (ebox a) := inferInstance

/- 4. Function field: codomain bound only — `a` stays unbounded (and is
   here uninhabited, so any spurious [Inhabited a] demand would fail). -/
example {b : Type} [Inhabited b] : Inhabited (fnbox Empty b) := inferInstance

/- 5. Parameterized records: container-headed fields -> unconditional
   (checked at an uninhabited element type); direct tyvar field ->
   bounded. -/
example : Inhabited (pfile Empty) := inferInstance
example {a : Type} [Inhabited a] : Inhabited (plabeled a) := inferInstance

/- 6. Only the last constructor usable -> unconditional instance. -/
example : Inhabited (third Empty) := inferInstance

/- 7. Deep container nesting -> unconditional. -/
example : Inhabited (deep Empty) := inferInstance

/- 8. Self-recursive parameterized type -> bounded via the
   non-recursive constructor. -/
example {a : Type} [Inhabited a] : Inhabited (wrapped2 a) := inferInstance

/- 9. April class 2: bounded Inhabited bases place no constraints on
   the BEq/Ord deriving chain. -/
example {a : Type} [Inhabited a] : Inhabited (boundedbase a) := inferInstance
example : (Chain (BB 1) (W2 CEmpty2 2) == Chain (BB 1) (W2 CEmpty2 2)) = true := rfl
