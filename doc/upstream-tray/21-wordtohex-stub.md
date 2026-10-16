# 21 — `Machine_word.wordToHex` (and so `show` on machine words) is a stub on OCaml, Isabelle and Coq

Target: `rems-project/lem`, `library/machine_word.lem`. State: **Draft**,
not filed. Drafted 2026-10-03.

## Affected code (upstream `3802cb0`)

`library/machine_word.lem:1363-1371`:

```lem
val wordToHex : forall 'a. mword 'a -> string
declare hol target_rep function wordToHex = `words$word_to_hex_string`
(* Building libraries fails if we don't provide implementations for the
   type class. *)
let {ocaml;isabelle;coq} wordToHex w = "wordToHex not yet implemented"

instance forall 'a. (Show (mword 'a))
  let show = wordToHex
end
```

lem-lean's copy is the same at lines 1370-1379 (it adds a Lean
representation).

## Classification

**INTENDED GAP.** The comment says the stub exists so that the library
builds. We report it because `show` on any machine word silently returns
the placeholder text instead of failing, so the gap is easy to miss in
output.

## Reproducer

Excerpt of `repro/mword/mword.lem` (driver `main.ml` next to it):

```lem
open import Pervasives_extra
open import Machine_word

let w8 (n : natural) : mword ty8 = wordFromNatural n

(* LP5: wordToHex / show *)
let lp5_hex () : string = wordToHex (w8 171)
let lp5_show () : string = show (w8 171)
```

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
upstream `ocaml-lib` compiled from the same checkout, OCaml 5.4.0,
zarith 1.14; conventions in README §4. Excerpt (full transcript:
`repro/mword/transcript-2026-10-03.txt`):

```
lp5_hex                = "wordToHex not yet implemented"
lp5_show               = "wordToHex not yet implemented"
```

## Observed vs expected

Observed: the placeholder string. Expected: a hexadecimal rendering (HOL4
`word_to_hex_string` gives one; for 171 something like `"AB"` or
`"0xAB"`, the format being the Lem authors' choice).

## Impact

Debug output and any `show`-based printing of machine words is
meaningless on OCaml, silently.

## Proposed remedy

An OCaml implementation in `ocaml-lib/lem.ml`, e.g.
`let wordToHex (_, w) = Z.format "%x" w` (zarith), with
``declare ocaml target_rep function wordToHex = `Lem.wordToHex` ``; Isabelle
and Coq can keep the stub or gain library definitions. At minimum, a stub
that fails loudly rather than returning text.

## Origin

lem-lean library-parity work, finding LP5: mainline
`doc/lean-backend/2026-09-30_library-parity-coverage.md` §2 item 1 and the
archived record `8ccbe40` §2 "LP5 — `wordToHex` / `show` on `mword` is a
stub on OCaml (QUESTION)", whose [AGENT] recommendation is "record as an
OCaml-library gap (upstream), keep Lean's real rendering". The tray scope
is the [USER 2026-10-03] ruling (all 16 findings, re-verified).

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
