import Lake
open Lake DSL

package CppModel where
  version := v!"0.1.0"
  moreLeanArgs := #["-DautoImplicit=false"]

require LemLib from "../../lean-lib"

@[default_target]
lean_lib CppModel where
  srcDir := "."
  roots := #[`Cmm]
