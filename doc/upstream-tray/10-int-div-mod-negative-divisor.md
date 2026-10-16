# 10 — OCaml `int`/`int32`/`int64` division and remainder with a negative divisor are neither floor nor Euclidean (and `integer` is Euclidean where the provers floor)

Target: `rems-project/lem`, `ocaml-lib/nat_num.ml` (OCaml runtime for
`Num`). State: **Draft**, not filed. Drafted 2026-10-03.

## Affected code (upstream `3802cb0`)

`ocaml-lib/nat_num.ml:12-34`:

```ocaml
let int_mod i n =
  let r = i mod n in
  if (r < 0) then r + n else r

let int_div i n =
  let r = i / n in
  if (i mod n < 0) then r - 1 else r
```

and the same shape for `int32_mod`/`int32_div`/`int64_mod`/`int64_div`.
The adjustment assumes a positive divisor. `library/num.lem` maps `intDiv`
and `intMod` to these (`:724`, `:738`; `int32` at `:914,929`, `int64` at
`:1107,1122`). HOL4 maps them to `/` and `%`, Isabelle to `div` and
`mod`, Coq to `Z.div` and `Zmod` — floor division with the remainder
taking the sign of the divisor. `integerDiv`/`integerMod` map to
`Nat_big_num.div`/`modulus` on OCaml (`:1298` …), which return the
Euclidean result.

`ocaml-lib/nat_num.ml` in lem-lean is byte-identical to upstream's.

## Classification

**TRUE BUG** for `int`/`int32`/`int64`: with a negative dividend and a
negative divisor the remainder can exceed the divisor in magnitude, which
no standard convention does. **UNCLEAR** for `integer`: OCaml is
Euclidean and the prover maps are floor; they differ when the divisor is
negative. Which convention Lem intends is not stated in `num.lem`.

## Reproducer

```lem
open import Pervasives

let int_dm     (a : int)     (b : int)     : int * int         = (a / b, a mod b)
let int32_dm   (a : int32)   (b : int32)   : int32 * int32     = (a / b, a mod b)
let int64_dm   (a : int64)   (b : int64)   : int64 * int64     = (a / b, a mod b)
let integer_dm (a : integer) (b : integer) : integer * integer = (a / b, a mod b)
```

with an OCaml driver printing `(q, r)` for several sign combinations
(`repro/divmod/`).

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
upstream `ocaml-lib` compiled from the same checkout, OCaml 5.4.0,
zarith 1.14; conventions in README §4. Full transcript
(`repro/divmod/transcript-2026-10-03.txt`):

```
$ lem -wl ign -ocaml divmod.lem
[lem exit 0]
$ ocamlfind ocamlopt -package zarith -linkpkg -I <upstream ocaml-lib> extract.cmxa divmod.ml main.ml -o divmod.exe
[ocamlopt exit 0]
$ ./divmod.exe
a=-7 b=-2 | int 2 -3 | int32 2 -3 | int64 2 -3 | integer 4 1
a=7 b=-2 | int -3 1 | int32 -3 1 | int64 -3 1 | integer -3 1
a=-7 b=2 | int -4 1 | int32 -4 1 | int64 -4 1 | integer -4 1
a=7 b=2 | int 3 1 | int32 3 1 | int64 3 1 | integer 3 1
a=-6 b=-2 | int 3 0 | int32 3 0 | int64 3 0 | integer 3 0
a=-7 b=-2^61 | int -1 -2305843009213693959 | int64 -1 -2305843009213693959 | integer 1 2305843009213693945
```

(The transcript's last line, `[run exit 0]`, is omitted here.)

## Observed vs expected

| a, b | OCaml `int` (q, r) | floor (HOL4/Isabelle/Coq) | Euclidean | OCaml `integer` |
|---|---|---|---|---|
| -7, -2 | (2, -3) | (3, -1) | (4, 1) | (4, 1) |
| 7, -2 | (-3, 1) | (-4, -1) | (-3, 1) | (-3, 1) |
| -7, 2 | (-4, 1) | (-4, 1) | (-4, 1) | (-4, 1) |
| -7, -2^61 | (-1, -2^61-7) | (0, -7) | (1, 2^61-7) | (1, 2^61-7) |

The floor and Euclidean columns are computed by hand from the definitions;
no prover was run. For a positive divisor all conventions agree, and so do
all OCaml results.

## Impact

`int`, `int32` and `int64` division by a negative number gives results
that match no prover target (and for `a=-7, b=-2^61` a remainder larger
than the divisor). `integer` division by a negative number agrees with
neither the floor convention of the prover maps nor `int`. Code that
divides by a possibly negative value (two's-complement arithmetic
models, address computations) can behave differently across targets.

## Proposed remedy

Decide the intended convention and implement it on all four OCaml types.
For floor (matching the prover maps): `let int_mod i n = let r = i mod n
in if r <> 0 && ((r < 0) <> (n < 0)) then r + n else r` and `int_div i n
= (i - int_mod i n) / n`, with the same for `Int32`/`Int64`, and
`Nat_big_num.div`/`modulus` replaced by floor variants (`Z.fdiv` and its
remainder). For Euclidean, the converse change on the prover side. Either
way, a sentence in `num.lem` saying which convention is meant.

## Origin

- lem-lean `doc/lean-backend/2026-09-03_parity-fix-record.md` §F1
  ("`int`/`int32`/`int64` div and mod (DISCREPANCY)"), which quotes
  `nat_num.ml:12-33` and records the fork's choice to mirror OCaml in its
  Lean library; noodle probe F1 found it.
- Archived record (lem-lean commit `8ccbe40`,
  `doc/lean-backend/2026-09-30_library-parity-coverage.md` §2 "F1 note —
  int/int32/int64 `mod` with a negative divisor (KNOWN)"): "`intMod -7 -2 =
  -3`, `intMod -7 -2^61 = -2^61-7` (|remainder| > |divisor|, neither floor
  nor Euclidean) … recorded here as an upstream-report candidate only."
  That record is [AGENT] work. The observation about `integer` is new in
  this tray (2026-10-03, [AGENT]).

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
