# Inhabited instance design for the Lean backend

## Problem

Lean 4's `partial def` requires `Inhabited T` for the return type. The Lem backend must generate `Inhabited` instances for all types. For types where it can't find a valid constructor (parametric types without nullary constructors, self-referential mutual types), it needs a fallback that:

- Does not panic at module init
- Does not require `[Inhabited a]` typeclass constraints
- Does not require `unsafe`
- Does not require user annotation
- Works uniformly for all types

## Solution

Two tiers, no heuristics:

**Tier 1 — real constructors.** When the backend can find a safe constructor (nullary, or non-self-referential), use it. This provides a real, useful default value.

**Tier 2 — `noncomputable instance (priority := low) ... := DAEMON`.** For everything else, uniformly. No sorry anywhere in Inhabited generation.

`DAEMON` is an axiom already defined in LemLib (`axiom DAEMON : ∀ {α : Type}, α`). It has no implementation and generates no init-time code. `noncomputable` tells Lean's code generator to skip the instance entirely. `priority := low` allows user-provided instances to override.

The `mutual def` infrastructure stays for tier 1 types in mutual blocks (they need forward references between real constructor defaults). Tier 2 types in mutual blocks are emitted as standalone `noncomputable instance` declarations outside the `mutual def` block — they don't reference other types so they don't need forward refs.

`declare {lean} skip_instances type T` remains available for types where the user wants to suppress ALL auto-generated instances (Inhabited + BEq/Ord/SetType/Eq0/Ord0) and provide everything externally.

## What `noncomputable` means in practice

Code that transitively calls `default` on a DAEMON-backed type gets a compile error: "depends on noncomputable definition." This is **intentional** — if a type has no valid default value, code that evaluates `default` on it is buggy. `noncomputable` turns a runtime panic (`sorry`) into a compile error. That's strictly better.

For types where the user genuinely needs a computable `Inhabited`, they use `skip_instances` and provide a hand-written instance. This is the same pattern the Cerberus team already uses for BEq/Ord on `ctype`.

## Examples

### Type with nullary constructor → tier 1 (real default)
```lem
type forest 'a = FNil | FCons of tree 'a * forest 'a
```
```lean
instance {a : Type} : Inhabited (forest a) where
  default := FNil
```

### Mutual types with safe constructors → tier 1 via mutual def
```lem
type ctype_ = Void | Integer of integerType | ...
and ctype = Ctype of list annot * ctype_
```
```lean
mutual
def ctype_.default_inhabited : ctype_ := Void
def ctype.default_inhabited : ctype := Ctype [] ctype_.default_inhabited
end
instance : Inhabited ctype_ where default := ctype_.default_inhabited
instance : Inhabited ctype where default := ctype.default_inhabited
```

### Parametric type, no nullary constructor → tier 2 (DAEMON)
```lem
type nd_action 'a = NDactive of 'a | NDkilled of nat
```
```lean
noncomputable instance (priority := low) {a : Type} : Inhabited (nd_action a) where
  default := DAEMON
```

### Self-referential mutual type → tier 2 (DAEMON)
```lem
type x 'a = N of y 'a
and y 'a = O of x 'a
```
```lean
noncomputable instance (priority := low) {a : Type} : Inhabited (x a) where
  default := DAEMON
noncomputable instance (priority := low) {a : Type} : Inhabited (y a) where
  default := DAEMON
```

### User needs computable Inhabited → skip_instances
```lem
type nd_action 'a = NDactive of 'a | NDkilled of nat
declare {lean} skip_instances type nd_action
```
```lean
-- (nothing generated — user provides in hand-written .lean file)
```

## Transitive cascade

Tier 2 cascades: if a constructor argument's type is tier 2 (DAEMON/noncomputable), then `default` on that argument is noncomputable. A type whose best constructor takes a tier 2 argument directly (not behind `List`/`Option`) cannot be tier 1.

The backend does NOT check this transitively. `find_safe_ctor_for_mutual` only checks for mutual type references within the same block, not whether argument types have computable Inhabited.

For **parametric types** this is already correct — the parametric path only uses nullary constructors (which don't reference other types), so DAEMON handles everything else.

For **monomorphic types** that instantiate a parametric tier-2 type (e.g., `type concrete_assertion = CA of cn_expr nat string`), the backend may incorrectly select tier 1 and generate `default := CA default` which fails to compile because `cn_expr`'s Inhabited is noncomputable.

When this happens, the compiler error is clear: "depends on noncomputable definition." The fix is `declare {lean} skip_instances type concrete_assertion` + a hand-written instance if one is actually needed. This is the correct behavior — these types genuinely have no computable default. The design ensures there is always a legitimate, non-hacky way to resolve the error.

## Impact on existing code

Code that currently calls `default` on a type with no valid constructor will get a compile error instead of a runtime panic. This may require adding `skip_instances` for types that either:

1. Genuinely need computable defaults (user provides hand-written instance)
2. Transitively depend on tier 2 types (the cascade — `skip_instances` suppresses the broken auto-generation)

A third option: marking downstream definitions as `noncomputable def` is also valid when the code only exists for type-checking (proofs, specifications) and doesn't need to run.

All three are improvements: they make implicit assumptions explicit and turn runtime panics into compile errors.

## Summary

| Condition | Generated instance |
|---|---|
| Nullary constructor found | `instance ... := CtorName` |
| Safe non-nullary constructor (mutual) | `instance ... := CtorName.default_inhabited` (via mutual def) |
| `skip_instances` declared | No instance |
| Everything else | `noncomputable instance (priority := low) ... := DAEMON` |
