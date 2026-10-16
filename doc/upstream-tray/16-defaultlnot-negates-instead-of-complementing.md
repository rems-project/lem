# 16 — `Word.defaultLnot` negates its argument instead of complementing it

Target: `rems-project/lem`, `library/word.lem` (definition shared by all
targets). State: **Draft**, not filed. Drafted 2026-10-03.

## Affected code (upstream `3802cb0`)

`library/word.lem:726-727`:

```lem
val defaultLnot : forall 'a. (bitSequence -> 'a) -> ('a -> bitSequence) -> 'a -> 'a 
let defaultLnot fromBitSeq toBitSeq x = fromBitSeq (bitSeqNegate (toBitSeq x))
```

`bitSeqNegate` (`:311-312`) is arithmetic negation
(`bitSeqArithUnaryOp integerNegate`); bitwise complement is `bitSeqNot`
(`:115-116`). Its siblings `defaultLand`, `defaultLor`, … (`:729-745`) use
the bitwise operations. No library instance uses `defaultLnot`: the `lnot`
instances are defined directly (`integerLnot i = ~(i + 1)`, `:751-752`;
`intLnot`, `:847-849`). lem-lean's copy is the same at lines 742-743.

## Classification

**TRUE BUG** (minor, currently unused in the library). The name and the
pattern of its siblings say bitwise complement; the body computes `-x`.

## Reproducer

```lem
open import Pervasives_extra
open import Word

let lu2_defaultLnot () : integer = defaultLnot integerFromBitSeq (bitSeqFromInteger Nothing) (~6)
let lu2_integerLnot () : integer = integerLnot (~6)
```

(Excerpt of `repro/libdefs/libdefs.lem`; driver `main.ml` next to it.)

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
upstream `ocaml-lib` compiled from the same checkout, OCaml 5.4.0,
zarith 1.14; conventions in README §4. Excerpt (full transcript:
`repro/libdefs/transcript-2026-10-03.txt`):

```
defaultLnot (-6)     = 6
integerLnot (-6)     = 5
```

## Observed vs expected

Observed: `defaultLnot … (-6) = 6`. Expected: `5`, the value of the
library's own `integerLnot (-6)` (`lnot x = -x - 1`). The definition is
shared, so every target computes 6 (only OCaml was run).

## Impact

None inside the library today. A user instance written in the style of
the siblings (`let lnot = defaultLnot fromBS toBS`) gets negation.

## Proposed remedy

`let defaultLnot fromBitSeq toBitSeq x = fromBitSeq (bitSeqNot (toBitSeq x))`,
and an assert such as `defaultLnot integerFromBitSeq (bitSeqFromInteger
Nothing) (~6) = 5`. Checked 2026-10-03 on the same build with the body
copied under another name (`fixedLnot`): on `[-6; 0; 5]` at `integer` it
returns `5; -1; -6`, i.e. `-x - 1`.

## Origin

lem-lean library-parity work, finding LU2: archived record only (lem-lean
commit `8ccbe40`, branch `archive/linksem-fixes-2026-09-30` of the linksem
checkout, `doc/lean-backend/2026-09-30_library-parity-coverage.md` §2 "LU2
— `defaultLnot` negates instead of complementing (LEM)": "No library
instance uses it … identical on both targets. Upstream candidate."). That
record is [AGENT] work; cut from mainline in the downscope of 2026-09-30,
brought back by the [USER 2026-10-03] ruling (all 16 findings, re-verified).

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
