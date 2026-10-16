# 08 — OCaml `mword`: rotation by 0 or by the width, and over-wide rotations and arithmetic shifts, raise `Invalid_argument`

Target: `rems-project/lem`, `ocaml-lib/lem.ml` (OCaml runtime for
`Machine_word`). State: **Draft**, not filed. Drafted 2026-10-03.

## Affected code (upstream `3802cb0`)

`ocaml-lib/lem.ml:226-231`:

```ocaml
let word_ror i (n,w) =
  let low = Big_int_impl.BI.extract_big_int w i n in
  let high = Big_int_impl.BI.extract_big_int w 0 i in
  (n, Nat_big_num.bitwise_or low (Big_int_impl.BI.shift_left_big_int high (n-i)))

let word_rol i (n,w) = word_ror (n-i) (n,w)
```

and `ocaml-lib/lem.ml:208-217`, `word_arithShiftRight`, which builds the
sign fill with `shift_left_big_int ones (n-m)`.

- `word_ror 0`: `extract_big_int w 0 0` has length 0 and raises.
- `word_rol n` is `word_ror 0`; `word_rol (n+1)` is `word_ror (-1)`.
- `word_ror (n+1)`: the shift count `n-i` is negative.
- `word_arithShiftRight` of a negative word by `m > n`: `n-m` is negative.

`rotateRight`, `rotateLeft` and `arithShiftRight` map here
(`library/machine_word.lem:1560,1566,1530`); HOL4 maps them to
`words$word_ror`, `words$word_rol` and `words$word_asr`, which are total.

`ocaml-lib/lem.ml` in lem-lean is byte-identical to upstream's.

## Classification

**TRUE BUG.** Rotation by 0 is the identity on every prover target, and
rotating or shifting by more than the width is defined there; the OCaml
runtime crashes on inputs the Lem functions' types admit.

## Reproducer

Excerpt of `repro/mword/mword.lem` (driver `main.ml` next to it; each
value is computed in a thunk so that the driver can report the exception):

```lem
open import Pervasives_extra
open import Machine_word

let w8 (n : natural) : mword ty8 = wordFromNatural n

(* OM5: rotations and arithmetic shifts *)
let om5_ror0 () : natural = naturalFromWord (rotateRight 0 (w8 1))
let om5_rol8 () : natural = naturalFromWord (rotateLeft 8 (w8 1))
let om5_rol9 () : natural = naturalFromWord (rotateLeft 9 (w8 1))
let om5_ror9 () : natural = naturalFromWord (rotateRight 9 (w8 1))
let om5_ror1 () : natural = naturalFromWord (rotateRight 1 (w8 1))
let om5_asr9 () : natural = naturalFromWord (arithShiftRight (w8 128) 9)
let om5_asr3 () : natural = naturalFromWord (arithShiftRight (w8 128) 3)
```

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
upstream `ocaml-lib` compiled from the same checkout, OCaml 5.4.0,
zarith 1.14; conventions in README §4. Excerpt (full transcript:
`repro/mword/transcript-2026-10-03.txt`):

```
om5_ror0               raises Invalid_argument("Z.extract: nonpositive bit length")
om5_rol8               raises Invalid_argument("Z.extract: nonpositive bit length")
om5_rol9               raises Invalid_argument("Z.extract: negative bit offset")
om5_ror9               raises Invalid_argument("Z.shift_left: count argument must be positive")
om5_ror1               = 128
om5_asr9               raises Invalid_argument("Z.shift_left: count argument must be positive")
om5_asr3               = 240
```

(`om5_ror1` and `om5_asr3` are controls that work.)

## Observed vs expected

| Expression (`ty8`) | OCaml | Expected (HOL4) |
|---|---|---|
| `rotateRight 0 1` | raises | 1 |
| `rotateLeft 8 1` | raises | 1 |
| `rotateLeft 9 1` | raises | 2 |
| `rotateRight 9 1` | raises | 128 |
| `arithShiftRight 128 9` | raises | 255 |

The expected values follow the definitions of the HOL4/Isabelle operators
that the library maps these functions to; no prover was run for this draft.

## Impact

A crash of the OCaml executable on well-typed input. Rotation amounts that
come from data (e.g. instruction semantics with a rotate-by-register) hit
0 and the width routinely.

## Proposed remedy

`word_ror`: reduce `i` modulo `n` and return the word unchanged when the
result is 0 (`n = 0` needs its own case). `word_rol`: the same, via
`word_ror ((n - i mod n) mod n)`. `word_arithShiftRight`: clamp `m` to `n`
(the result is all ones for a negative word).

## Origin

lem-lean library-parity work, finding OM5: archived record (lem-lean
commit `8ccbe40`, branch `archive/linksem-fixes-2026-09-30` of the linksem
checkout, `doc/lean-backend/2026-09-30_library-parity-coverage.md` §2 "OM5
— OCaml rotations and arithmetic shifts raise (OCAML)"), carried into
mainline `doc/lean-backend/2026-09-30_library-parity-coverage.md` §2 item 6.
The recommendation is [AGENT]: "the OCaml failures are bugs (rotation by 0
is the identity in every prover backend)"; the tray scope is
the [USER 2026-10-03] ruling (all 16 findings, re-verified).

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
