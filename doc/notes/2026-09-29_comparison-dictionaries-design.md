# Comparison dictionaries and function-field comparisons (linksem audit A1)

Date: 2026-09-29. [USER 2026-09-29] approved the audit fixes; design
[AGENT]. Finding: `doc/lean-backend/2026-09-28_linksem-findings.md`, audit
follow-up A1.

## Problem

Lem's DEFAULT instances of `Eq` and `SetType` (and `MapKeyType`, via
`SetType`) are OCaml's polymorphic comparison: available at every type, no
dictionary. On the Lean target the comparison at a type `T args` is a
bounded structural instance (`[Ord a] → SetType (T a)`, `[BEq a] → Eq0 (T
a)`). Two gaps made Lean diverge:

1. **Unconstrained type variables.** A generic definition such as linksem's
   `tag_image {abifeature}` compares `range_tag abifeature` values, but no
   `[Ord abifeature]` is in scope. Lean resolved to a priority-50 fallback
   instance whose methods called `failwithI`; a panic continues with a
   default value (see A2), so sets kept duplicates (`tag_image` twice: OCaml
   2 tags, Lean 3) and the linksem linker built an executable with entry
   point 0 and no `.text`. ~200 fallback sites in linksem.
2. **Function-typed fields.** A type such as `amd64_abi_feature` (`GOT of
   list (... function ...)`) had instances that panicked on EVERY
   comparison, where OCaml's polymorphic compare raises only when it
   reaches a closure (`GOT [] = GOT []` is fine).

## Design

**(i) Function fields.** Types with function-typed fields go through the
existing structural derivation (`generate_derived_comparisons`, the
OCaml-rank path). A new shape `CSfn` compares a function-typed position with
LemLib's `lemFunctionalCompare`/`lemFunctionalBeq`, which fail with OCaml's
message `compare: functional value`; containers containing functions
(list/maybe/either/tuple) are recursed into like sibling references. The
comparison fails whenever it reaches a closure. That is exactly when
OCaml's `=` fails, but NOT always when OCaml's `compare` fails: `compare`
returns 0 for the same closure object (physical equality) and raises only
for distinct closures. Correction of 2026-09-30 (review finding
MEDIUM-1): this is the open discrepancy A1-R in
`doc/lean-backend/2026-09-28_linksem-findings.md`, with the probe
`p_fn_compare_same_closure`. A shape the derivation cannot
recurse through keeps a loud residual (fails only if reached), with an
accurate reason.

**(ii) Dictionary threading** (`lean_cmp_prepass`, run per module before
emission, accumulating across the modules of one lem invocation). For every
use of a constant inside a definition:
- a Lem class constraint (`Eq` → Lean `BEq`; `SetType`/`MapKeyType`/`Ord`
  → Lean `Ord`) instantiated at a type: follow Lem's own instance
  resolution (`Types.get_matching_instance`). An EXPLICIT instance (tuples,
  lists, maybe, ...) passes the demand to its constraints; the DEFAULT
  instance demands the Lean class on every type variable of the type; a
  bare type variable demands it unless the definition carries that Lem
  constraint itself;
- a polymorphic-compare primitive (`unsafe_structural_equality`,
  `defaultCompare`, ...: the default instances' inlined methods) demands
  the Lean class on the variables of its instantiation;
- a generated definition that received threaded binders demands them at
  its instantiation (transitive; fixpoint).
Only the enclosing definition's own type variables are bound. Binders are
emitted after the Lem constraints (`[Ord a]`/`[BEq a]`); explicit `@f` uses
get one extra `_` per threaded binder.

**No fallback.** The priority-50 "unconstrained type variable" residual
instances are deleted: a demand the analysis misses is a Lean COMPILE error.

## Evidence

- `tests/comprehensive/test_cmp_threading.lem` (generic insert, transitive
  generic caller, equality, explicit tuple instance): passes; pristine
  c2a68e7 output panics with the residual messages and fails 3 of 4 asserts.
- `tests/comprehensive/test_fn_field_compare.lem`: set order and equality of
  function-field values without reaching a function.
- linksem: the whole model compiles with no fallback instance; the audit's
  minimal case (`tag_image` twice) gives OCaml's `1 2 2` with zero panics.
- LemLib's generated modules are unchanged (all their comparisons go through
  explicit instances or carry Lem constraints).
