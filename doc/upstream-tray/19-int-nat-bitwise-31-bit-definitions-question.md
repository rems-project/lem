# 19 — Question: `int`/`nat` bitwise operations are 31-bit by definition (used by HOL4, Isabelle, Coq) but native 63-bit on OCaml

Target: `rems-project/lem`, `library/word.lem`. State: **Draft**, not
filed. Drafted 2026-10-03.

## Affected code (upstream `3802cb0`)

`library/word.lem`:

- `:839-844`: `intFromBitSeq bs = intFromInteger (integerFromBitSeq
  (resizeBitSeq (Just 31) bs))` and `bitSeqFromInt i = bitSeqFromInteger
  (Just 31) (integerFromInt i)`; the `nat` versions at `:1008` and `:1012`
  likewise use 31 bits.
- `intLor`, `intLxor`, `intLand`, `intLsl`, `intAsr` (`:856-888`) and
  `natLor`, `natLand`, `natLsl`, `natAsr`, … (`:1015-1048`) are defined through
  `defaultLor intFromBitSeq bitSeqFromInt` etc., and have OCaml target
  representations only (`land`, `lor`, `lxor`, `lsl`, `asr`, e.g. `:873`,
  `:881`, `:1017`, `:1033`).

So HOL4, Isabelle and Coq run the 31-bit definitions, and OCaml runs its
native 63-bit operators. The upstream-generated Isabelle library shows it
(`Lem_word.thy`, generated with `lem -isa` from this checkout):

```
944:definition bitSeqFromInt  :: \<open> int \<Rightarrow> bitSequence \<close>  where 
945:     \<open> bitSeqFromInt i = ( bitSeqFromInteger (Some(( 31 :: nat))) ( i))\<close> 
1002:definition intLsl  :: \<open> int \<Rightarrow> nat \<Rightarrow> int \<close>  where 
1003:     \<open> intLsl i n = ( defaultLsl intFromBitSeq bitSeqFromInt i n )\<close> 
```

lem-lean's copy keeps these definitions (its line numbers are shifted by
its Lean representations).

## Classification

**UNCLEAR / question.** `num.lem` says `int` is "bounded size integers
with uncertain length" (`:135`) but maps it to the provers' unbounded
`int`/`Z` (`:138-141`), and says the prover targets map `nat` to unbounded
numbers (`:103-110`). On the provers the
arithmetic of `int` is therefore unbounded while its bitwise operations
wrap at 31 bits, and the two targets disagree from `2^30` on. We cannot
tell whether 31 is a deliberate choice (the old OCaml 32-bit `int`?) or a
leftover.

## Reproducer

The definitions can be executed on OCaml by calling them directly, which
shows what the prover targets compute:

```lem
open import Pervasives
open import Word

(* OCaml target: the target_rep (native 63-bit lsl/lor/land). *)
let rep_lsl  : int = intLsl 1 30
let rep_lor  : int = intLor 1073741824 0
let rep_nlor : nat = natLor 1099511627776 1

(* The library's own definitions, which HOL4, Isabelle and Coq use
   (those targets have no target_rep for these functions). *)
let def_lsl  : int = defaultLsl intFromBitSeq bitSeqFromInt 1 30
let def_lor  : int = defaultLor intFromBitSeq bitSeqFromInt 1073741824 0
let def_nlor : nat = defaultLor natFromBitSeq bitSeqFromNat 1099511627776 1
```

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
upstream `ocaml-lib` compiled from the same checkout, OCaml 5.4.0,
zarith 1.14; conventions in README §4. Full transcript
(`repro/bitwise/transcript-2026-10-03.txt`):

```
$ lem -wl ign -ocaml bitwise.lem
[lem exit 0]
$ ocamlfind ocamlopt -package zarith -linkpkg -I <upstream ocaml-lib> extract.cmxa bitwise.ml main.ml -o bitwise.exe
[ocamlopt exit 0]
$ ./bitwise.exe
intLsl 1 30:          rep 1073741824  def 0
intLor 2^30 0:        rep 1073741824  def -1073741824
natLor 2^40 1:        rep 1099511627777  def 1
[run exit 0]
```

## Observed vs expected

Observed: `intLsl 1 30` is `2^30` on OCaml and `0` by the definition;
`intLor (2^30) 0` is `-2^30` by the definition; `natLor (2^40) 1` is `1`.
Expected: we do not know which is intended; either way the targets should
agree on inputs both represent.

## Impact

Any Lem development that uses bitwise operations on `int`/`nat` (rather
than `integer`/`natural` or machine words) proves things on HOL4/Isabelle/
Coq about a 31-bit operation and runs a 63-bit one on OCaml.

## Possible remedies (for the Lem authors)

1. If `int`/`nat` are meant to be unbounded on the provers (as `num.lem`
   says), define the bitwise operations on them unboundedly, e.g. through
   `integer` (`bitSeqFromInteger Nothing`), as `integerLor` etc. already
   are (`:758` and following).
2. If a fixed width is meant, document it in `num.lem`/`word.lem` and
   make the OCaml representations agree (mask to the width).

## Origin

lem-lean library-parity work, finding LP4 (lem-lean mainline
`doc/lean-backend/2026-09-30_library-parity-coverage.md` §1 "LP4: int/nat
bitwise were 31-bit on Lean (ACCEPTED: ruled OCaml-target deviation,
2026-09-30)"; the archived record `8ccbe40` §2 "LP4" with the same
numbers as above). The fork's Lean target now uses unbounded operations
and treats the OCaml wrap as a deviation: [USER 2026-09-30] agreed items
1-3. The question of whether "the 31-bit prover definitions
(LP4) go into the upstream Lem report bundle" was left open there
(§3 item 4) and is answered by the [USER 2026-10-03] ruling (all 16 findings, re-verified).

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
