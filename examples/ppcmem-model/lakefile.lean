import Lake
open Lake DSL

package PpcmemModel where
  version := v!"0.1.0"
  moreLeanArgs := #["-DautoImplicit=false"]

require LemLib from "../../lean-lib"

@[default_target]
lean_lib PpcmemModel where
  srcDir := "."
  roots := #[`BitwiseCompatibility, `MachineDefUtils, `MachineDefFreshIds,
             `MachineDefValue, `MachineDefTypes, `MachineDefInstructionSemantics,
             `MachineDefStorageSubsystem, `MachineDefThreadSubsystem,
             `MachineDefSystem, `MachineDefAxiomaticCore]
