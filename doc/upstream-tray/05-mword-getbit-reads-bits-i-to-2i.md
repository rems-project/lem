# 05 — OCaml `mword`: `getBit w i` tests bits `i..2i` instead of bit `i`

Target: `rems-project/lem`, `ocaml-lib/lem.ml` (OCaml runtime for
`Machine_word`). State: **Draft**, not filed. Drafted 2026-10-03.

## Affected code (upstream `3802cb0`)

`ocaml-lib/lem.ml:194-196`:

```ocaml
let word_getBit (n,w) i =
  let bit = Big_int_impl.BI.extract_big_int w i (i+1) in
  if Nat_big_num.equal bit Nat_big_num.zero then false else true
```

`extract_big_int w ofs len` takes an offset and a LENGTH
(`word_lsb` at `:203` uses `extract_big_int w 0 1` for one bit). Here the
length is `i+1`, so the result is non-zero when any of bits `i..2i` is
set. `getBit` maps to it at `library/machine_word.lem:1477`; HOL4 maps
`getBit` to `words$word_bit`, Isabelle to `bit`.

`ocaml-lib/lem.ml` in lem-lean is byte-identical to upstream's.

## Classification

**TRUE BUG.** The length argument is evidently meant to be `1`, as in
`word_lsb` and `bitlistFromWord` (`:173`); the function is correct only
for `i = 0` or when bits `i+1..2i` are clear.

## Reproducer

Excerpt of `repro/mword/mword.lem` (one file shared by drafts 05-09 and
21; driver `main.ml` next to it):

```lem
open import Pervasives_extra
open import Machine_word

let w8 (n : natural) : mword ty8 = wordFromNatural n

let om2_getbit_4_1 () : bool = getBit (w8 4) 1   (* 4 = 0b100: bit 1 is 0 *)
let om2_getbit_8_2 () : bool = getBit (w8 8) 2   (* 8 = 0b1000: bit 2 is 0 *)
let om2_getbit_2_1 () : bool = getBit (w8 2) 1   (* control: bit 1 is 1 *)
```

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
upstream `ocaml-lib` compiled from the same checkout, OCaml 5.4.0,
zarith 1.14; conventions in README §4. Excerpt of the run (full
transcript: `repro/mword/transcript-2026-10-03.txt`):

```
om2_getbit_4_1         = true
om2_getbit_8_2         = true
om2_getbit_2_1         = true
```

## Observed vs expected

Observed: `true`, `true`, `true`. Expected (HOL4 `word_bit`, Isabelle
`bit`): `false`, `false`, `true`.

The expected values follow the definitions of the HOL4/Isabelle operators
that the library maps these functions to; no prover was run for this draft.

## Impact

Silent wrong answers for any bit test above bit 0 on the OCaml target,
whenever a higher bit within `i+1..2i` is set. Specifications that decode
flags or fields bit by bit (instruction encodings, ELF flags) compute
different results on OCaml and on the provers.

## Proposed remedy

`let bit = Big_int_impl.BI.extract_big_int w i 1 in` (or
`Z.testbit w i`).

## Origin

lem-lean library-parity work, finding OM2: recorded in the archived
record (lem-lean commit `8ccbe40`, branch `archive/linksem-fixes-2026-09-30`
of the linksem checkout, `doc/lean-backend/2026-09-30_library-parity-coverage.md`
§2 "OM2 — OCaml `getBit i` reads bits i..2i (OCAML)") and carried into
mainline `doc/lean-backend/2026-09-30_library-parity-coverage.md` §2 item 3.
The record's recommendation is [AGENT]: "treat OM1–OM5 as OCaml-library
bugs, keep Lean on the prover semantics, and send them upstream". The
operator's ruling of 2026-10-03 put every such finding in this tray
([USER 2026-10-03]: all 16 findings, re-verified).

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
