# 06 — OCaml `mword`: negating zero gives the out-of-range value `2^n` (also via `wordFromInteger` and `signedDivide`)

Target: `rems-project/lem`, `ocaml-lib/lem.ml` (OCaml runtime for
`Machine_word`). State: **Draft**, not filed. Drafted 2026-10-03.

## Affected code (upstream `3802cb0`)

`ocaml-lib/lem.ml:148-150`:

```ocaml
let word_uminus (n,w) =
  let lim = Big_int_impl.BI.shift_left_big_int Big_int_impl.BI.unit_big_int n in
  (n,Nat_big_num.sub lim w)
```

For `w = 0` the result is `2^n`, outside the representation's invariant
"length and in-range bignum" (comment at `:124-125`). `word_equal` (`:129`)
compares the bignums, so the result is not equal to the zero word.
`uminus` maps here (`library/machine_word.lem:1615`); the OCaml-only
definitions of `wordFromInteger` (`:1648-1651`, `uminus` of the magnitude)
and `signedDivide` (`:1633-1638`) inherit it. HOL4 maps `uminus` to
`words$word_2comp`, Isabelle to unary `-`.

`ocaml-lib/lem.ml` in lem-lean is byte-identical to upstream's.

## Classification

**TRUE BUG.** Addition, subtraction and multiplication reduce modulo
`2^n` (`word_bin_arith`, `:233-239`); negation does not, and its result
violates the representation invariant.

## Reproducer

Excerpt of `repro/mword/mword.lem` (driver `main.ml` next to it):

```lem
open import Pervasives_extra
open import Machine_word

let w8 (n : natural) : mword ty8 = wordFromNatural n

(* OM1: negation *)
let om1_uminus_zero () : natural = naturalFromWord (uminus (w8 0))
let om1_uminus_zero_eq () : bool = (uminus (w8 0) = w8 0)
let om1_from_integer () : natural = naturalFromWord (wordFromInteger (~256) : mword ty8)
let om1_signed_divide () : natural = naturalFromWord (signedDivide (w8 255) (w8 5))
```

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
upstream `ocaml-lib` compiled from the same checkout, OCaml 5.4.0,
zarith 1.14; conventions in README §4. Excerpt (full transcript:
`repro/mword/transcript-2026-10-03.txt`):

```
om1_uminus_zero        = 256
om1_uminus_zero_eq     = false
om1_from_integer       = 256
om1_signed_divide      = 256
```

## Observed vs expected

| Expression (`ty8`) | OCaml | Expected (HOL4 `word_2comp`/`i2w`/`word_quot`) |
|---|---|---|
| `naturalFromWord (uminus 0)` | 256 | 0 |
| `uminus 0 = 0` | false | true |
| `naturalFromWord (wordFromInteger (-256))` | 256 | 0 |
| `naturalFromWord (signedDivide 255 5)` (i.e. -1 / 5) | 256 | 0 |

The expected values follow the definitions of the HOL4/Isabelle operators
that the library maps these functions to; no prover was run for this draft.

## Impact

Silent wrong values on the OCaml target: any negation of zero, any
`wordFromInteger` of a negative multiple of `2^n`, and any signed division
with a zero quotient and operands of opposite sign. The out-of-range value
then propagates (e.g. it compares unequal to zero).

## Proposed remedy

Reduce the result:
`(n, Big_int_impl.BI.extract_big_int (Nat_big_num.sub lim w) 0 n)`, or
return `(n, zero)` when `w` is zero.

## Origin

lem-lean library-parity work, finding OM1: archived record (lem-lean
commit `8ccbe40`, branch `archive/linksem-fixes-2026-09-30` of the linksem
checkout, `doc/lean-backend/2026-09-30_library-parity-coverage.md` §2 "OM1
— OCaml `mword` negation not reduced (OCAML)"), carried into mainline
`doc/lean-backend/2026-09-30_library-parity-coverage.md` §2 item 2. The
recommendation to send OM1–OM5 upstream is [AGENT]; the tray scope is
the [USER 2026-10-03] ruling (all 16 findings, re-verified).

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
