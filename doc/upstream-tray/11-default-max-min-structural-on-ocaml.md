# 11 — OCaml backend: the default `max`/`min` use OCaml's structural `max`/`min`, ignoring the type's `Ord` instance

Target: `rems-project/lem`, `library/basic_classes.lem` (OCaml target
representation). State: **Draft**, not filed. Drafted 2026-10-03.

## Affected code (upstream `3802cb0`)

`library/basic_classes.lem:238-249`:

```lem
val defaultMax : forall 'a. Ord 'a => 'a -> 'a -> 'a
let inline defaultMax = maxByLessEqual (<=)
declare ocaml    target_rep function defaultMax = `max`

val defaultMin : forall 'a. Ord 'a => 'a -> 'a -> 'a
let inline defaultMin = minByLessEqual (<=)
declare ocaml    target_rep function defaultMin = `min`

default_instance forall 'a. Ord 'a => ( OrdMaxMin 'a) 
  let max = defaultMax
  let min = defaultMin
end
```

The Lem definition uses the type's `Ord` instance; the OCaml
representation is `Stdlib.max`/`min`, which use OCaml's structural order.
HOL4, Isabelle and Coq use the Lem definition. lem-lean's copy is the same
at lines 258-269 (Lean additions only).

## Classification

**TRUE BUG.** The OCaml representation is correct only when the type's
`Ord` instance coincides with OCaml's structural order. For any type with
a user `Ord` instance and no `OrdMaxMin` instance of its own, `max` and
`min` on OCaml ignore that instance.

## Reproducer

```lem
open import Pervasives_extra

type r = R of nat
let r_cmp (R a) (R b) = compare b a
instance (Ord r)
  let compare = r_cmp
  let (<) x y = (r_cmp x y = LT)
  let (<=) x y = (r_cmp x y <> GT)
  let (>) x y = (r_cmp x y = GT)
  let (>=) x y = (r_cmp x y <> LT)
end
let lp1_le () : bool = (R 1 <= R 2)
let lp1_max () : r = max (R 1) (R 2)
let lp1_min () : r = min (R 1) (R 2)
let lp1_maxBy () : r = maxByLessEqual (<=) (R 1) (R 2)
```

(Excerpt of `repro/libdefs/libdefs.lem`, shared with drafts 12, 16
and 20; driver `main.ml` next to it.) The generated OCaml for the two
middle lines is `(max (R 1) (R 2))` and `(min (R 1) (R 2))`.

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
upstream `ocaml-lib` compiled from the same checkout, OCaml 5.4.0,
zarith 1.14; conventions in README §4. Excerpt (full transcript:
`repro/libdefs/transcript-2026-10-03.txt`):

```
R 1 <= R 2           = false
max (R 1) (R 2)      = R 2
min (R 1) (R 2)      = R 1
maxByLessEqual (<=) (R 1) (R 2) = R 1
```

## Observed vs expected

The instance orders `R 2` below `R 1` (`R 1 <= R 2` is false). Observed:
`max` gives `R 2`, `min` gives `R 1`. Expected (the Lem definition, which
the same program evaluates as `maxByLessEqual (<=)` on the last line):
`max` gives `R 1`, `min` gives `R 2`.

## Impact

Silent wrong results for `max`/`min` on OCaml at any type with a
non-structural `Ord` instance (reversed orders, orders on one field of a
record, orders on abstract keys). Values that are equal under the
instance but structurally different are also chosen differently.

## Proposed remedy

Drop the two OCaml `target_rep` declarations so that OCaml uses the Lem
definition, or keep `Stdlib.max`/`min` only through specific instances for
the base types where structural order is the instance (`nat`, `int`,
`natural`, …), which may already exist.

## Origin

lem-lean library-parity work, finding LP1: archived record only (lem-lean
commit `8ccbe40`, branch `archive/linksem-fixes-2026-09-30` of the linksem
checkout, `doc/lean-backend/2026-09-30_library-parity-coverage.md` §2 "LP1
— `defaultMax`/`defaultMin` are structural on OCaml (QUESTION)"; the
record's reproducer is the one above). The record's recommendation is
[AGENT]: "treat as an OCaml-target deviation (an upstream report: the rep
is only valid when the instance is structural)". The finding was cut from
mainline in the downscope of 2026-09-30 ([USER 2026-09-30]: an
aggressive downscope after some drift on the lem-lean
build); the tray scope that brings it back is the [USER 2026-10-03] ruling
(all 16 findings, re-verified).

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
