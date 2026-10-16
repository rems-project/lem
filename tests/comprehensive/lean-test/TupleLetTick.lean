/- Hand-written support for test_tuple_let_once.lem (the m7
   single-evaluation pin): a process-global counter behind a
   hand-written impure-extern pattern (unsafe impl + implemented_by
   opaque). Since the effect-retirement arc deleted the backend's
   effectful mechanism (runEffectful + generated attribute armour),
   the pure-typed boundary AND its armour live entirely in this test
   scaffold.

   ARMOUR PLACEMENT (audit F1, 2026-09-01 — the outer attributes
   alone are NOT enough): closed-term extraction reaches THROUGH
   outer attributes. With never_extract only on tickPair/tickPairImpl,
   the compiler extracts the closed application `unsafeBaseIO
   tickPairIO` INSIDE tickPairImpl into a module-init cached constant
   (IR: tickPairImpl___closed__0) — the action runs once at init, and
   even a duplicated-RHS emitter reads the same cached pair, so the
   pin goes vacuous. The extracted closed term contains only
   `unsafeBaseIO` and `tickPairIO`; extraction is blocked by marking
   the constants the closed term MENTIONS — hence `never_extract,
   noinline` on tickIO and tickPairIO themselves (and on the
   impl/opaque pair against call-site caching/CSE one level up). With
   the full set, the number of RHS evaluations is observable in the
   values the destructuring let binds: one evaluation gives (1, 2); a
   duplicated RHS gives the second binding (3, 4) — plant-verified
   red-green against the reverted m7 emitter (see the L2 record
   addendum). This models exactly the class of hand-written impure
   externs that the retirement leaves to consumers' own armour. -/

namespace TupleLetTick

@[never_extract, noinline]
private unsafe def counterImpl : IO.Ref Nat :=
  unsafeBaseIO (IO.mkRef 0)

@[implemented_by counterImpl]
private opaque counter : IO.Ref Nat

@[never_extract, noinline]
private def tickIO : BaseIO Nat :=
  counter.modifyGet (fun n => (n + 1, n + 1))

@[never_extract, noinline]
private def tickPairIO : BaseIO (Nat × Nat) := do
  let a ← tickIO
  let b ← tickIO
  pure (a, b)

@[never_extract, noinline]
private unsafe def tickPairImpl (_ : Unit) : Nat × Nat :=
  unsafeBaseIO tickPairIO

@[implemented_by tickPairImpl]
opaque tickPair : Unit → Nat × Nat

attribute [never_extract] tickPair

end TupleLetTick
