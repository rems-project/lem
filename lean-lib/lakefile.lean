import Lake
open Lake DSL

package LemLib where
  version := v!"0.1.0"

@[default_target]
lean_lib LemLib where
  srcDir := "."
  globs := #[.one `LemLib, .submodules `LemLib]

/-- Pset/Pmap representation invariants over bounded-exhaustive operation
    sequences + kernel-checked examples of the OCaml observables the ports
    reproduce. Building it IS running it. -/
@[default_target]
lean_lib LemLibTest where
  srcDir := "."
  globs := #[.one `LemLibTest]

/-- Kernel-checked equalities between the tail-recursive list/string
    rewrites and the definitions they replaced. -/
@[default_target]
lean_lib LemLibTheorems where
  srcDir := "."
  globs := #[.one `LemLibTheorems]

/-- Lookup-after-insert laws for the `Pmap`/`Fmap` port under a
    strict-weak-order comparator: `WF`, `WF_add`, `find?_add_same`,
    `find?_add_other`, the `Fmap` corollaries; kernel-only, `#print axioms`. -/
@[default_target]
lean_lib LemLibPmapLaws where
  srcDir := "."
  globs := #[.one `LemLibPmapLaws]
