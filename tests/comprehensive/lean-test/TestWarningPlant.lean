/-! Negative plant for the package's `-DwarningAsError=true` (TODO item 54,
    2026-11-07): the two warning kinds the backend used to emit, written by
    hand. NOT a default target: the Makefile's lean-unreferenced-binders
    builds this module (`lake build WarningPlant`) and REQUIRES the build
    to fail with both as errors — proof that the flag bites, so that the
    suite's zero-warning claim is a gate, not a report. -/

def plantUnreferenced (x : Nat) (y : Nat) : Nat := x

def plantInert (x : Nat) : Nat := x
termination_by structural x
