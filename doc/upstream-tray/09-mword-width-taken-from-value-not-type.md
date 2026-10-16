# 09 — OCaml `mword`: `wordFromBitlist`, `word_extract` and `word_concat` take the result width from their arguments, not from the result type

Target: `rems-project/lem`, `ocaml-lib/lem.ml` (OCaml runtime for
`Machine_word`). State: **Draft**, not filed. Drafted 2026-10-03.

## Affected code (upstream `3802cb0`)

The OCaml representation is `type mword = int * Nat_big_num.num`, a width
and a value (`ocaml-lib/lem.ml:124-127`: "we represent bitvectors as a
length (so that only the creation operations need a length parameter) and
in-range bignum"). Three operations whose Lem types fix the result width
compute it from their arguments instead:

- `wordFromBitlist` (`:162-168`): width = length of the list;
- `word_extract lo hi` (`:138-140`): width = `hi-lo+1`;
- `word_concat` (`:135-136`): width = `n1+n2`.

Their Lem types are `list bool -> mword 'a`, `nat -> nat -> mword 'a ->
mword 'b` and `mword 'a -> mword 'b -> mword 'c`
(`library/machine_word.lem:1373-1376,1454-1457,1447-1450`); none passes the
`Size` of the result type to the OCaml function (`wordFromBitlist` has a
`Size 'a` constraint whose dictionary the OCaml representation does not
take; the other two have no `Size` constraint). HOL4 maps
them to `bitstring$v2w`, `words$word_extract` and `words$word_concat`,
whose results have the width of the result type.

`ocaml-lib/lem.ml` in lem-lean is byte-identical to upstream's.

## Classification

**TRUE BUG**, with a design component: the representation deliberately
carries the width, but these three functions then produce words whose
width disagrees with their Lem type, and a too-long bit list produces a
value out of range for the type.

## Reproducer

Excerpt of `repro/mword/mword.lem` (driver `main.ml` next to it):

```lem
open import Pervasives_extra
open import Machine_word

let w8 (n : natural) : mword ty8 = wordFromNatural n
let w4 (n : natural) : mword ty4 = wordFromNatural n

(* OM4: width from the value, not the type *)
let om4_bitlist4_len () : nat = word_length (wordFromBitlist [true; false; true; true] : mword ty8)
let om4_bitlist4_bits () : nat = length (bitlistFromWord (wordFromBitlist [true; false; true; true] : mword ty8))
let om4_bitlist11 () : natural = naturalFromWord (wordFromBitlist [true; false; false; false; false; false; false; false; false; true; true] : mword ty8)
let om4_extract_len () : nat = word_length (word_extract 0 3 (w8 171) : mword ty8)
let om4_concat_len () : nat = word_length (word_concat (w4 10) (w4 5) : mword ty16)
```

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
upstream `ocaml-lib` compiled from the same checkout, OCaml 5.4.0,
zarith 1.14; conventions in README §4. Excerpt (full transcript:
`repro/mword/transcript-2026-10-03.txt`):

```
om4_bitlist4_len       = 4
om4_bitlist4_bits      = 4
om4_bitlist11          = 1027
om4_extract_len        = 4
om4_concat_len         = 8
```

## Observed vs expected

| Expression | OCaml | Expected (type width) |
|---|---|---|
| `word_length (wordFromBitlist [t;f;t;t] : mword ty8)` | 4 | 8 |
| `length (bitlistFromWord (… same …))` | 4 | 8 |
| `naturalFromWord (wordFromBitlist <11 bits, 0b10000000011> : mword ty8)` | 1027 | 3 (low 8 bits, as HOL4 `v2w`) |
| `word_length (word_extract 0 3 (171 : ty8) : mword ty8)` | 4 | 8 |
| `word_length (word_concat (10 : ty4) (5 : ty4) : mword ty16)` | 8 | 16 |

The numeric value agrees with the prover targets whenever the result type
is at least as wide as the computed width; `word_length`,
`bitlistFromWord`, `msb` and signed interpretations do not. The expected
column follows the HOL4 definitions; no prover was run.

## Impact

Silent disagreement with the prover targets on the width of words built
from lists, extracts and concatenations whenever the annotated type is not
the "natural" width; an out-of-range value for a too-long bit list.

## Proposed remedy

Pass the result type's `Size` to these three functions (as
`wordFromNatural` already does via `ocaml_inject (size, n)`,
`library/machine_word.lem:1361`) and normalise with
`machine_word_inject`. If the Lem authors prefer the current behaviour,
document that on OCaml these functions are only meaningful when the
result type equals the computed width.

## Origin

lem-lean library-parity work, finding OM4: archived record (lem-lean
commit `8ccbe40`, `doc/lean-backend/2026-09-30_library-parity-coverage.md`
§2 "OM4 — OCaml word size taken from the value, not the type (OCAML)"),
carried into mainline `doc/lean-backend/2026-09-30_library-parity-coverage.md`
§1 "LP6/LP7 width question" and §2 item 5, measured there by the probe
`p_mword_width`. The fork ruled it an OCaml-target deviation for its own
Lean target: [USER 2026-09-30] agreed items 1-3. The tray
scope is the [USER 2026-10-03] ruling (all 16 findings, re-verified).

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
