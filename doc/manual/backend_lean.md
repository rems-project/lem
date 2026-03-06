## Lean 4

The command line option `-lean` instructs Lem to generate Lean 4 output. A module with name `Mymodule` generates a file `Mymodule.lean`.

### Compilation
Lem-generated Lean code depends on a Lem-specific Lean library found in the `lean-lib/` directory. This library (`LemLib`) provides helper definitions used by the generated output, such as set and map operations, comparison functions, and numeric utilities. To use the generated code, set up a [Lake](https://lean-lang.org/lean4/doc/setup.html) project that imports `LemLib`.

The generated Lean files also import a `Pervasives` module corresponding to the Lem pervasives library. This module can be generated from the Lem library using `lem -lean library/pervasives.lem` (or `pervasives_extra.lem`), or provided as a stub that re-exports `LemLib`.

### Relationship to Coq Backend
The Lean backend is structurally modelled on the Coq backend, as Lean 4 and Coq are similar in many respects. Key differences in the generated output include:

- Lean 4 syntax: `structure`/`where` for records, `inductive` for datatypes, `def` for definitions
- Unicode operators: `→`, `×`, `∀`, `∃` instead of ASCII equivalents
- Native record update syntax: `{ r with field := value }`
- Constructor dot notation in patterns: `.Red` instead of `Red`
- `Inhabited` typeclass instances instead of Coq-style `_default` definitions
- `sorry` for undefined/opaque terms instead of Coq's `DAEMON`

