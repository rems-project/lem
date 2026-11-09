#!/usr/bin/env python3
"""Text pins for the unreferenced-binder rule and the per-definition
`termination_by` (TODO item 54, 2026-11-07; record
doc/lean-backend/2026-11-07_unreferenced-binders-record.md), over the
generated Test_unreferenced_binders.lean (test_unreferenced_binders.lem):

  U2  no identifier gains a second underscore: a source name already spelled
      `_x` is left as it is (pre-merge review F1; Lean accepts `__x` silently,
      so this is a text pin, not a compile one).
  U1  every binding form's unreferenced variable is bound as `_<name>` and
      every referenced or kept one under its source name — one exact line
      per form (def parameters, lambda, match arm, `function` arm, nested
      tuple pattern, let pattern, named pattern, local lambda, shadowing,
      a partial def's parameter, equation clauses, an instance method, a do
      line, a top-level destructuring let's per-name projections, a fuel'd
      worker whose sentinel names an otherwise unreferenced parameter; a
      name already spelled `_x`, unreferenced and referenced; a nested arm
      binder spelled like the sentinel's parameter and a nested lambda
      binder spelled like the structural parameter, both underscored — the
      kept names protect the clause head only, pre-merge review F3).
  T1  `termination_by structural` is attached to exactly the derived
      comparison and size definitions that recurse (a self-call or a cycle
      through the emitted block): present on the recursive type, the
      recursive member of the mutual block, the option-field type and its
      option helpers; absent on the non-recursive type, the block member
      outside every cycle and the member that only calls into the cycle.
  V   vacuity: the file has the definitions the pins name.

Plants (each run once on a scratch copy; the record quotes the failures):
  P1  `(_y : Nat)` edited back to `(y : Nat)` in def_params      -> U1 FAIL
  P2  the clause under rec_t.beq_derived deleted                  -> T1 FAIL
  P3  a `termination_by structural cmpx_` added under
      nonrec_t.beq_derived                                        -> T1 FAIL
"""
import re
import sys

if len(sys.argv) != 2:
    print("usage: check_unreferenced_binders.py Test_unreferenced_binders.lean")
    sys.exit(2)
path = sys.argv[1]
try:
    text = open(path, encoding="utf-8").read()
except OSError as e:
    print(f"  FAIL: cannot read {path}: {e}")
    sys.exit(1)
lines = text.split("\n")
fail = 0

# U1: exact lines.
expected = [
    "def def_params (x : Nat) (_y : Nat) : Nat := x",
    "def lambda_params : Nat → Nat → Nat := fun (_x : Nat) (y : Nat) => y",
    "  | some _v => 0",                       # match_arm
    "    | some _v => 7",                     # function_arm (under the compiled lambda)
    "  | (a, (_b, c)) => a + c",              # tuple_arm
    "  | (a, _b) => a",                       # let_pattern (compiled to a match)
    "  | y@((_x, w)) => (Prod.fst y, (w + 2))",  # as_pattern
    "  let f : Nat → Nat → Nat := fun (x : Nat) (_y : Nat) => x;",  # local_fun
    "partial def rec_unused (_tag : Nat) (l : List Nat) : Nat :=",
    "  | (0 : Nat), (_y : Nat) => 1",         # eq_clauses, first clause
    "  | (n : Nat), (_y : Nat) => n",         # eq_clauses, second clause
    "    tag_of _x := 42",                    # instance method
    "    let (_x : Nat) ← return0 (1 : Nat)",  # do line
    "  let (ta, _tb) : (Nat × Nat) := lemLetRhs_ta_tb",  # projection of ta
    "  let (_ta, tb) : (Nat × Nat) := lemLetRhs_ta_tb",  # projection of tb
    "def loop_lemFuel (lemFuel : Nat) (tag : Nat) (n : Nat) : Nat :=",  # kept: the sentinel names tag
    "  | 0 => (fuelExhausted tag)",
    # pre-merge review F1: a source name already spelled `_x` is left as it is
    "def keep_us (_x : Nat) (y : Nat) : Nat := y",
    "def use_us (_x : Nat) : Nat := _x + 1",
    # pre-merge review F3: the kept names protect the clause head only
    "def loop_arm_lemFuel (lemFuel : Nat) (tag : Nat) (o : Option Nat) : Nat :=",
    "     | some _tag => (loop_arm_lemFuel lemFuel) 7 none",
    "  | _ :: l2 => (fun (_l : List Nat) => 1) ([] : List Nat) + slen l2",
    "termination_by structural l",
]
for e in expected:
    if e not in lines:
        print(f"  FAIL (U1): {path} lacks the line: {e}")
        fail = 1
# arm_us: the arm's `_v` stays `_v` (F1); pinned as a block since `| some _v => 0` also belongs to match_arm
if not re.search(r"^def arm_us \(o : Option Nat\) : Nat :=\n  match o with\n  \| some _v => 0\n  \| none => 1$", text, re.M):
    print(f"  FAIL (U1): {path} lacks the arm_us block (an arm binder already spelled `_v` left as it is)")
    fail = 1
# U2 (F1): no identifier anywhere in the module's code gains a second underscore
# (the carried-over comments are stripped first: the probe's own comment quotes `__x`)
code = re.sub(r"/-.*?-/", "", text, flags=re.S)
dbl = [(i, l) for i, l in enumerate(code.split("\n"), 1) if re.search(r"(?<![A-Za-z0-9_'])__[A-Za-z0-9_']", l)]
if dbl:
    print(f"  FAIL (U2): {path} has a double-underscore identifier: line {dbl[0][0]}: {dbl[0][1].strip()}")
    fail = 1
# shadowed: the outer binder is `_x`, the inner let rebinds `x` and the body is `x`
shadow = re.search(r"^def shadowed : Nat → Nat :=\n  fun \(_x : Nat\) =>\n\s+let x := \(5 : Nat\);\n\s+x$", text, re.M)
if not shadow:
    print(f"  FAIL (U1): {path} lacks the shadowing shape (outer `_x`, inner `let x`, body `x`)")
    fail = 1

# T1: the clause per definition.
defs = {}
name = None
for l in lines:
    m = re.match(r"^(?:partial |private |@\[noinline\] private )?def (\S+)", l)
    if m:
        name = m.group(1)
        defs[name] = False
        continue
    if l.startswith("termination_by") and name is not None:
        defs[name] = True
    if l.startswith("theorem ") or l.startswith("instance ") or l.startswith("inductive "):
        name = None
with_clause = [
    "rec_t.beq_derived", "rec_t.compare_derived", "rec_t.lemSize",
    "mA.beq_derived", "mA.compare_derived", "mA.lemSize",
    "ot.beq_derived", "ot.compare_derived", "ot.lemSize", "ot.lemSize_aux1",
]
without_clause = [
    "nonrec_t.beq_derived", "nonrec_t.compare_derived",
    "mB.beq_derived", "mB.compare_derived", "mB.lemSize",
    "mC.beq_derived", "mC.compare_derived", "mC.lemSize",
]
for d in with_clause:
    if d not in defs:
        print(f"  FAIL (V): {path} has no definition {d}")
        fail = 1
    elif not defs[d]:
        print(f"  FAIL (T1): {d} recurses but carries no termination_by clause")
        fail = 1
for d in without_clause:
    if d not in defs:
        print(f"  FAIL (V): {path} has no definition {d}")
        fail = 1
    elif defs[d]:
        print(f"  FAIL (T1): {d} does not recurse but carries a termination_by clause (inert: Lean warns)")
        fail = 1
# ot's option helpers (one per comparison kind; numbered on demand) are in the cycle
helpers = [d for d in defs if re.match(r"^ot\.(beq|cmp)_deriv_aux\d+$", d)]
if len(helpers) != 2:
    print(f"  FAIL (V): expected two option helpers for ot, found {helpers}")
    fail = 1
for d in helpers:
    if not defs[d]:
        print(f"  FAIL (T1): {d} is in a cycle with ot's comparison but carries no clause")
        fail = 1
if "nonrec_t.lemSize" in defs:
    print("  FAIL (T1): nonrec_t is not recursive but has a derived lemSize")
    fail = 1

if fail:
    sys.exit(1)
n_clause = sum(1 for v in defs.values() if v)
n_derived = len(with_clause) + len(helpers)
print(f"  OK: {len(expected) + 2} binder lines as pinned, no double underscore; termination_by on exactly the {n_derived} derived "
      f"definitions that recurse (plus {n_clause - n_derived} structural declare) of {len(defs)}; none on the {len(without_clause)} derived ones that do not")
