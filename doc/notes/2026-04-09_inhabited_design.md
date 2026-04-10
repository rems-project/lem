# Inhabited instance design for the Lean backend

## Problem

Lean 4's `partial def` requires `Inhabited T` for the return type. The Lem backend auto-generates `Inhabited` instances for all types. For types where it can't find a valid constructor (parametric types without nullary constructors, mutually recursive types with no escape), it needs a fallback.

The fallback must satisfy these constraints:
- **No init-time panic**: `sorry` in a zero-arg def/instance is eagerly evaluated at module init, crashing before `main` runs
- **No typeclass constraints**: `[Inhabited a]` defeats `partial def` (constraints not available at call sites)
- **No `unsafe`**: taints downstream code
- **No user annotation**: should work automatically

## Solution: `noncomputable instance` with `DAEMON`

LemLib already defines:

```lean
axiom DAEMON : ∀ {α : Type}, α   -- lean-lib/LemLib.lean:18
```

Combined with `noncomputable`, this satisfies all constraints:

```lean
noncomputable instance {a : Type} : Inhabited (nd_action a) where
  default := DAEMON
```

**Why this works:**
- `DAEMON` is an axiom — no implementation, no init-time code
- `noncomputable` tells the code generator to skip this instance entirely
- Lean's type checker sees the `Inhabited` instance, which is all `partial def` needs
- No `[Inhabited a]` constraints needed — `DAEMON` is unconditional
- No `unsafe` — axioms are safe declarations

**Verified** on Lean 4.28.0: compiles with zero errors, `partial def` works, `#eval` confirms no init panic.

## Inhabited generation strategy

The backend uses a tiered approach:

| Priority | Condition | Generated default | Example |
|---|---|---|---|
| 1 | `skip_instances` declared | No instance at all | User provides externally |
| 2 | Nullary constructor found | Real constructor | `FNil`, `Void0`, `Red` |
| 3 | Safe non-nullary constructor (monomorphic) | Real constructor via `mutual def` | `Ctype [] ctype_.default_inhabited` |
| 4 | Everything else | `noncomputable instance` with `DAEMON` | Parametric types, circular mutuals |

Priority 2 and 3 provide real, useful defaults. Priority 4 is the safe fallback for types where no real default can be constructed automatically.

## What this replaces

The `declare {lean} inhabited type T = \`expr\`` feature (added in `e9553e9`, fixed in `706b658`) is no longer needed. `noncomputable` + `DAEMON` handles all the cases that `inhabited` was designed for, without requiring user annotations or expressions.

The `declare {lean} skip_instances type T` feature is still useful for BEq/Ord/SetType/Eq0/Ord0, where the user wants to provide real comparison logic in a hand-written Lean file.

## Examples

### Parametric type, no nullary constructor
```lem
type nd_action 'a = NDactive of 'a | NDkilled of nat
```
```lean
-- Generated: DAEMON fallback (NDactive needs 'a, NDkilled needs Nat — but DAEMON is simpler)
noncomputable instance {a : Type} : Inhabited (nd_action a) where
  default := DAEMON
```

### Parametric type WITH nullary constructor
```lem
type forest 'a = FNil | FCons of tree 'a * forest 'a
```
```lean
-- Generated: real constructor (FNil is nullary, no type args needed)
instance {a : Type} : Inhabited (forest a) where
  default := FNil
```

### Monomorphic mutual types
```lem
type ctype_ = Void | Integer of integerType | ...
and ctype = Ctype of list annot * ctype_
```
```lean
-- Generated: real constructors via mutual def
mutual
def ctype_.default_inhabited : ctype_ := Void
def ctype.default_inhabited : ctype := Ctype [] ctype_.default_inhabited
end
instance : Inhabited ctype_ where default := ctype_.default_inhabited
instance : Inhabited ctype where default := ctype.default_inhabited
```

### Type with skip_instances (user-controlled)
```lem
type ctype_ = ...
declare {lean} skip_instances type ctype_
```
```lean
-- Generated: nothing (user provides in CerbCtypeInstances.lean)
```

## Summary of Lem annotations for Lean instances

| Annotation | Effect |
|---|---|
| *(none)* | Auto-generate all instances (real constructors or DAEMON fallback) |
| `declare {lean} skip_instances type T` | Suppress ALL auto-generated instances; user provides externally |
