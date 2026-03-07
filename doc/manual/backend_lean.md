## Lean 4

The command line option `-lean` instructs Lem to generate Lean 4 output. A module with name `Mymodule` generates a file `Mymodule.lean` and possibly `Mymodule_auxiliary.lean`.

### Compilation
Lem-generated Lean code depends on a Lem-specific Lean library found in the `lean-lib/` directory. This library (`LemLib`) provides helper definitions used by the generated output, such as set and map operations, comparison functions, and numeric utilities. Running `make lean-libs` in Lem's main directory generates Lean versions of the Lem library files in this directory.

To compile the generated code, set up a [Lake](https://lean-lang.org/lean4/doc/setup.html) project that depends on `LemLib`. A minimal `lakefile.lean` looks like:

    import Lake
    open Lake DSL

    package MyProject where
      version := v!"0.1.0"

    require LemLib from "path/to/lem/lean-lib"

    @[default_target]
    lean_lib MyLib where
      roots := #[`MyModule]

Then run `lake build` to compile. Lem has been tested against Lean 4.28.0.

The generated Lean files import a `Pervasives` module corresponding to the Lem pervasives library. This module is generated as part of `make lean-libs`. Alternatively, a stub that re-exports `LemLib` can be provided.

### Auxiliary Files
Lean auxiliary files contain executable tests generated from *assertions* in the input files, as well as proof obligations from *lemmata* and *theorems*. They are compiled alongside the main files by `lake build`. Assertions generate `#eval` commands that check the boolean expression at build time, printing PASS/FAIL results. Lemmata and theorems generate `theorem` declarations with `by decide`, which succeeds for decidable propositions. The command line option `-auxiliary_level auto` allows generating only the executable assertion tests.

### Recursive Definitions
All recursive function definitions are marked `partial` in the generated Lean output, since Lean 4 requires termination proofs for non-partial definitions. This is conservative but correct: the generated code will compile without requiring termination proofs.

### Inductive Relations
Lem inductive relation definitions are translated to Lean `inductive` types with a `Prop`-valued conclusion. For example, a Lem relation `indreln add : nat -> nat -> nat -> bool` generates `inductive add : Nat → Nat → Nat → Prop where`.

### Automatic Derivation
The Lean backend automatically derives `BEq` instances for generated inductive types and records, provided none of their constructor arguments have function types. This allows equality testing on most generated types without manual instance declarations.

### Automatic Renaming
Lean 4 types and values share a single namespace, unlike many other backends. The Lean backend automatically renames constants that would collide with type names in the same module. Additionally, certain names that clash with Lean 4 standard library type classes (such as `Add`, `Sub`, `Neg`, `Mul`, `Div`, `Mod`, `Pow`, `Min`, `Max`, `Abs`, `Not`, `Append`) are automatically renamed to avoid ambiguity.

### Relationship to Coq Backend
The Lean backend is structurally modelled on the Coq backend, as Lean 4 and Coq are similar in many respects. Key differences in the generated output include:

- Lean 4 syntax: `structure`/`where` for records, `inductive` for datatypes, `def` for definitions
- Unicode operators: `→`, `×`, `∀`, `∃` instead of ASCII equivalents
- Native record update syntax: `{ r with field := value }`
- Constructors brought into scope via `open TypeName` after each `inductive` definition
- `Inhabited` typeclass instances generated for all types (uses `sorry` for recursive types without base cases)
- `BEq` derivation for types without function-typed arguments
- `sorry` for undefined/opaque terms instead of Coq's `DAEMON`
- `partial` for all recursive definitions instead of requiring termination proofs

