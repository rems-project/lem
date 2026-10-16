# 12 — `Set.splitMember` returns the elements above the pivot first, the reverse of `Set.split`

Target: `rems-project/lem`, `library/set.lem` (definition shared by all
targets). State: **Draft**, not filed. Drafted 2026-10-03.

## Affected code (upstream `3802cb0`)

`library/set.lem:374-379`:

```lem
val split : forall 'a. SetType 'a, Ord 'a => 'a -> set 'a -> set 'a * set 'a
let split p s = (filter ((>) p) s, filter ((<) p) s)
declare {hol} rename function split = SET_SPLIT

val splitMember : forall 'a. SetType 'a, Ord 'a => 'a -> set 'a -> set 'a * bool * set 'a
let splitMember p s = (filter ((<) p) s, p IN s, filter ((>) p) s)
```

`((>) p)` is `fun x -> p > x` (the elements below `p`), so `split` returns
(below, above). `splitMember` uses the two sections the other way round
and returns (above, member, below). The assert `split_simple` (`:381-384`)
pins `split`'s order; there is no assert for `splitMember`. lem-lean's
copy is the same text at lines 395-400.

## Classification

**TRUE BUG** (by consistency). No comment states the intended order, but
`split` in the same file, the assert on it, and OCaml's `Set.split` (whose
`(below, member, above)` shape `splitMember` evidently imitates) all put
the lower part first.

## Reproducer

```lem
open import Pervasives_extra

let lu1_split () : set nat * set nat = Set.split 3 {1; 2; 3; 4; 5}
let lu1_splitMember () : set nat * bool * set nat = Set.splitMember 3 {1; 2; 3; 4; 5}
```

(Excerpt of `repro/libdefs/libdefs.lem`; driver `main.ml` next to it.)

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
upstream `ocaml-lib` compiled from the same checkout, OCaml 5.4.0,
zarith 1.14; conventions in README §4. Excerpt (full transcript:
`repro/libdefs/transcript-2026-10-03.txt`):

```
split 3 {1..5}       = ({1; 2}, {4; 5})
splitMember 3 {1..5} = ({4; 5}, true, {1; 2})
```

## Observed vs expected

Observed: `splitMember 3 {1..5} = ({4; 5}, true, {1; 2})`. Expected:
`({1; 2}, true, {4; 5})`. Because the definition is shared, every target
computes the observed value (only OCaml was run).

## Impact

Any caller that follows the `split`/OCaml convention gets the halves
swapped, silently, on every target. No caller in the Lem library itself
(`grep` finds none outside `set.lem`).

## Proposed remedy

`let splitMember p s = (filter ((>) p) s, p IN s, filter ((<) p) s)`,
plus an assert mirroring `split_simple`. If some user relies on the
current order, a changelog line.

## Origin

lem-lean library-parity work, finding LU1: archived record only (lem-lean
commit `8ccbe40`, branch `archive/linksem-fixes-2026-09-30` of the linksem
checkout, `doc/lean-backend/2026-09-30_library-parity-coverage.md` §2 "LU1
— `Set.splitMember` returns its halves swapped (LEM)": "Identical on both
targets (lem definition). Upstream report candidate."). That record is
[AGENT] work; cut from mainline in the downscope of 2026-09-30, brought
back by the [USER 2026-10-03] ruling (all 16 findings, re-verified).

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
