# 20 — Question: on OCaml, `Set.bigunionBy cmp` ignores `cmp` (the result keeps the member sets' comparator)

Target: `rems-project/lem`, `ocaml-lib/pset.ml` and the `*By` set
interface in `library/set.lem`. State: **Draft**, not filed. Drafted
2026-10-03.

## Affected code (upstream `3802cb0`)

- `library/set.lem:445,449`: `val bigunionBy : forall 'a. ('a -> 'a ->
  ordering) -> set (set 'a) -> set 'a`, with only an OCaml representation,
  `Pset.bigunion`; `bigunion` is `bigunionBy setElemCompare` on OCaml
  (`:450`).
- `ocaml-lib/pset.ml:501-502`: `let bigunion c xss = fold union xss
  (empty c)`, and `:313`: `let union s1 s2 = { s1 with s = union s1.cmp
  s1.s s2.s }`. Each step is `union x acc`, which keeps `x`'s comparator,
  so `c` is used only when every member set is empty (and for the empty
  accumulator).

`ocaml-lib/pset.ml` in lem-lean is byte-identical to upstream's (lem-lean's
own Lean library passes the comparator explicitly, which is how the
difference was noticed).

## Classification

**UNCLEAR / question.** Nothing in `set.lem` states what a `*By`
function's comparator means when it disagrees with the comparator the
argument sets were built with. On the run below OCaml's answers are the
mathematically expected ones (the union of `{1}` and `{4}` has two
elements), so this is not a wrong value; the question is whether the
comparator argument is meant to be authoritative, and whether mixing
comparators is meant to be allowed at all (by reading `pset.ml`, `union` of two sets built with
different comparators merges one set's tree under the other's order;
not exercised here).

## Reproducer

```lem
open import Pervasives_extra

let m3 (x : nat) (y : nat) : ordering = compare (x mod 3) (y mod 3)
let rev (x : nat) (y : nat) : ordering = compare y x
let lp9_size () : nat = Set.size (Set.bigunionBy m3 {{1}; {4}})
let lp9_list () : list nat = Set_extra.toList (Set.bigunionBy rev {{1; 2}; {3}})
```

(Excerpt of `repro/libdefs/libdefs.lem`; driver `main.ml` next to it.)

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
upstream `ocaml-lib` compiled from the same checkout, OCaml 5.4.0,
zarith 1.14; conventions in README §4. Excerpt (full transcript:
`repro/libdefs/transcript-2026-10-03.txt`):

```
size (bigunionBy m3 {{1}; {4}})  = 2
toList (bigunionBy rev {{1; 2}; {3}}) = [1; 2; 3]
```

## Observed vs expected

Observed: `cmp` has no effect (under `m3`, 1 and 4 are equal, yet the
result has 2 elements; under `rev` the elements are listed ascending).
Expected: unclear — that is the question. If `cmp` were authoritative the
answers would be `1` and `[3; 2; 1]`.

## Impact

Low for ordinary use (callers pass the elements' own comparator). The
interface suggests a control that the implementation does not give.

## Possible remedies (for the Lem authors)

1. Document that `*By` comparators must agree with the argument sets'
   comparator (and that otherwise the result is unspecified).
2. Or make `Pset.bigunion` (and siblings) rebuild under `c`.

## Origin

lem-lean library-parity work, finding LP9: archived record only (lem-lean
commit `8ccbe40`, branch `archive/linksem-fixes-2026-09-30` of the linksem
checkout, `doc/lean-backend/2026-09-30_library-parity-coverage.md` §2 "LP9
— `*By` set operations with a comparator other than the members'
(QUESTION)", with the same two reproducer lines). That record's [AGENT]
view: "using a `*By` comparator that disagrees with the members' `SetType`
is outside what the Pset port can mirror without carrying comparators in
the value; needs a ruling". Cut from mainline in the downscope of
2026-09-30; brought back by the [USER 2026-10-03] ruling (all 16 findings, re-verified). The
classification as a question rather than a bug is [AGENT] (this tray),
because the OCaml answers are the mathematically expected ones.

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
