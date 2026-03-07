import Lake
open Lake DSL

package LemLib where
  version := v!"0.1.0"

@[default_target]
lean_lib LemLib where
  srcDir := "."
  globs := #[.one `LemLib, .submodules `LemLib]
