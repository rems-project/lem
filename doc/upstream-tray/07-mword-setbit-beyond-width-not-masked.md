# 07 — OCaml `mword`: `setBit` at an index beyond the width stores an out-of-range value

Target: `rems-project/lem`, `ocaml-lib/lem.ml` (OCaml runtime for
`Machine_word`). State: **Draft**, not filed. Drafted 2026-10-03.

## Affected code (upstream `3802cb0`)

`ocaml-lib/lem.ml:187-192`:

```ocaml
let word_setBit (n,w) i b =
  let bit = Big_int_impl.BI.shift_left_big_int Big_int_impl.BI.unit_big_int i in
  if b then
    (n,Nat_big_num.bitwise_or w bit)
  else
    (n,Nat_big_num.bitwise_and w (snd (word_not (n,bit))))
```

For `i >= n` the `true` case ORs in `2^i` without masking; the word keeps
width `n` but its value is out of range. `setBit` maps here
(`library/machine_word.lem:1471`); HOL4 maps it to `$:+` (which leaves the
word unchanged for an index beyond the width), Isabelle to `set_bit`.

`ocaml-lib/lem.ml` in lem-lean is byte-identical to upstream's.

## Classification

**TRUE BUG.** The result violates the representation invariant ("length
and in-range bignum", `:124-125`) and disagrees with the prover targets.

## Reproducer

Excerpt of `repro/mword/mword.lem` (driver `main.ml` next to it):

```lem
open import Pervasives_extra
open import Machine_word

let w8 (n : natural) : mword ty8 = wordFromNatural n

(* OM3: setBit beyond the width *)
let om3_setbit_10 () : natural = naturalFromWord (setBit (w8 0) 10 true)
let om3_setbit_10_len () : nat = word_length (setBit (w8 0) 10 true)
```

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
upstream `ocaml-lib` compiled from the same checkout, OCaml 5.4.0,
zarith 1.14; conventions in README §4. Excerpt (full transcript:
`repro/mword/transcript-2026-10-03.txt`):

```
om3_setbit_10          = 1024
om3_setbit_10_len      = 8
```

## Observed vs expected

Observed: an 8-bit word whose value is 1024. Expected (HOL4 `:+`): the word
unchanged, value 0. (Whether an out-of-range index should instead be an
error is the Lem authors' choice; an out-of-range value is not a
meaningful answer either way.)

The expected values follow the definitions of the HOL4/Isabelle operators
that the library maps these functions to; no prover was run for this draft.

## Impact

A malformed word that later operations treat inconsistently (`word_length`
says 8; `naturalFromWord` says 1024; equality with any well-formed `ty8`
word is false).

## Proposed remedy

Mask the result to `n` bits (`extract_big_int … 0 n`), or ignore indices
`>= n`, matching HOL4.

## Origin

lem-lean library-parity work, finding OM3: archived record (lem-lean
commit `8ccbe40`, branch `archive/linksem-fixes-2026-09-30` of the linksem
checkout, `doc/lean-backend/2026-09-30_library-parity-coverage.md` §2 "OM3
— OCaml `setBit` beyond the width (OCAML)"), carried into mainline
`doc/lean-backend/2026-09-30_library-parity-coverage.md` §2 item 4. The
recommendation to send OM1–OM5 upstream is [AGENT]; the tray scope is
the [USER 2026-10-03] ruling (all 16 findings, re-verified).

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
