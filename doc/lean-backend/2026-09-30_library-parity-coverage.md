# Library parity coverage: record, scoped to arc/linksem (2026-09-30)

This record covers the Lem standard-library parity changes that are on the
branch `arc/linksem`: the fixes LP3, LP6, LP7 and LP8, and LP4, which is
ACCEPTED as a ruled OCaml-target deviation (commit `66e3cf8`; ruling of
2026-09-30, see LP4). Their
regression probes are `p_lib_word_int_nat`, `p_lib_machine_word` and
`f_lib_chr_range` in `tests/comprehensive/parity/`. It also records what
those probes exclude and why, and the rulings those exclusions need.
Worker [AGENT] unless marked. Reference semantics: the OCaml target,
except OCaml's hard-coded machine limits ([USER 2026-09-03],
`2026-09-03_exception-case-rulings.md`: the 63-bit `nat`/`int` wrap and the
raising `int_of_big_int`/`int32_of_big_int` conversions are deviations;
the logical semantics wins there).

## 0. Scope, and what was cut

The fixes were found by a wider coverage effort on another checkout
(branch `linksem/lib-probes` in `linksem-lean/deps/lem-lean`). It had 10
`p_lib_*` probes, 17 `f_lib_*` failure probes and a coverage tool,
`tests/comprehensive/parity/tools/lib_coverage.py`. It also had a longer
version of this record, with findings LP1, LP2, LP5, LP9, OM1–OM5, LU1, LU2
and THE, and a per-module coverage table (557 of 569 eligible library vals
referenced). [USER 2026-09-30]: an aggressive downscope followed some
drift on the lem-lean build. The wider probe set,
the tool and the longer record were cut in that downscope. They are
preserved, not merged, in commit `8ccbe40` ("Parity lane: library coverage
probes, coverage tool, record (library-parity-coverage)") on branch
`archive/linksem-fixes-2026-09-30` of `/home/dev/projects/linksem-lean/deps/lem-lean`.

Nothing from `8ccbe40` is imported here except the text below that
describes what this branch contains. Each claim was re-checked against
this branch. The coverage numbers are NOT claimed for this branch: its
library probes are the two above plus `f_lib_chr_range`.

## 1. Changes on this branch (commit `66e3cf8`)

### LP3: `natLand`/`natLor`/… were ambiguous on Lean (FIXED)

`lean-lib/LemLib.lean` had root-level helpers `natLand`, `natLor`,
`natLxor`, `natLnot`, `natLsl`, `natLsr` and `natAsr`, for
`library/transform.lem`. They collided with the generated
`Lem_Word.natLand` and its siblings, so any direct call from a Lem program
was a Lean build error (`Ambiguous term`). Fix: they are renamed `lemNat*`
(LemLib, "Nat bitwise operations"), and the `transform.lem` reps follow.
Regression: `p_lib_word_int_nat` calls the Word functions by name. The
names are now also in `library/lean_constants` (review fix 2026-09-30,
LOW d; see the findings record).

### LP4: int/nat bitwise were 31-bit on Lean (ACCEPTED: ruled OCaml-target deviation, 2026-09-30)

`library/word.lem` gives `intLand`, `intLor`, `intLxor`, `intLsl`, `intAsr`
and `natLand`, `natLor`, `natLxor`, `natLsl`, `natAsr` OCaml reps (native
`land`/`lor`/`lxor`/`lsl`/`asr`). They had no Lean rep, so Lean ran Lem's
definitions through a 31-bit `bitSequence`
(`bitSeqFromInt = bitSeqFromInteger (Just 31)`). The two targets disagreed
from 2^30 on (from the `8ccbe40` record: `intLsl 1 30` gave OCaml
`1073741824` and Lean `0`). [AGENT] change, ACCEPTED by the ruling of
2026-09-30 (below): the Lean reps are UNBOUNDED two's
complement (LemLib `lemIntLand`/`lemIntLor`/`lemIntLxor`/`lemIntLsl`/
`lemIntAsr` over `Int`, `lemNat*` over `Nat`). `intFromBitSeq` and
`bitSeqFromInt` keep Lem's 31-bit definition on every target. Regression:
`p_lib_word_int_nat` (459 pinned lines, operands up to 2^62-1), plus
LemLibTest examples for each sign case.

**The three targets disagree.** OCaml's reps are 63-bit and wrap. HOL,
Isabelle and Coq have no rep, so they run Lem's 31-bit `bitSequence`
definition. Lean's reps are unbounded.

**Ruling D2** [USER 2026-09-30]: agreed. It came
with the orchestrator's conditions: LP4 is ACCEPTED (Lean's bitwise reps
are unbounded two's complement) SUBJECT TO a measurement confirming that
the OCaml backend's reps for `intLand`/`Lor`/`Lxor`/`Lsl`/`Asr` and the nat
versions compute unbounded (big-integer) results, not 63-bit wrapping. The
proof asked for is a parity probe with operands beyond 2^63 showing that
the two targets agree, or a verbatim report of any disagreement.

**Measurement: the condition is NOT met.** Lem `nat` and `int` are native
OCaml `int` (`library/num.lem:117`), and OCaml cannot write a literal at or
above 2^62, so the wide operands are computed. Two probes, split in review
round 2 so that each measures one thing:

- `p_word_bitwise_wide` has no arithmetic. Every operand is a literal
  inside 62 bits or the result of `lsl`. Registered class `ruled` (by the
  ruling below; it was `open` until then).
- `p_word_bitwise_wide_mul` holds the rows whose wide operands are built
  by multiplication. The multiplication itself wraps on OCaml
  (`p61*4 = 0`), which is the separately ruled X3/N4 class, so these rows
  do not isolate the bitwise operations. Registered class `ruled` (X3/N4).
  The X3 record says the arithmetic wrap has "no runner row by design".
  This row exists [AGENT] because since review round 2 a registered
  probe's Lean side is pinned exactly, so the row pins the known
  difference instead of absorbing new ones.

The parity runner's diff for the round-1 version of the probe, which
mixed both kinds of row, verbatim (`<` is the OCaml reference, `>` is
Lean; the three control rows inside 62 bits agree). The first nine
differing rows are bitwise-only and are unchanged in the split
`p_word_bitwise_wide`, which replaces the multiplication rows with
`lsl`-built operands (for example OCaml `intLor (intLsl 1 63) 1 = 1`
against Lean `9223372036854775809`; pins `expected/p_word_bitwise_wide.out`
and `.lean.out`):

```
< intLsl 1 62 = -4611686018427387904
< intLsl 1 63 = 0
< intLsl 3 62 = -4611686018427387904
< intLsl 1 64 = 1
< intAsr (intLsl 1 63) 1 = 0
< natLsl 1 62 = -4611686018427387904
< natLsl 1 63 = 0
< natLsl 5 61 = 2305843009213693952
< natAsr (natLsl 1 63) 1 = 0
< operand p61*4 (2^63): 0
< intLor (p61*4) 1 = 1
< intLand (p61*4) (p61*4) = 0
< intLxor (p61*8) 1 = 1
< natLor (n61*4) 1 = 1
< natLand (n61*4) (n61*4) = 0
< natLxor (n61*8) 1 = 1
---
> intLsl 1 62 = 4611686018427387904
> intLsl 1 63 = 9223372036854775808
> intLsl 3 62 = 13835058055282163712
> intLsl 1 64 = 18446744073709551616
> intAsr (intLsl 1 63) 1 = 4611686018427387904
> natLsl 1 62 = 4611686018427387904
> natLsl 1 63 = 9223372036854775808
> natLsl 5 61 = 11529215046068469760
> natAsr (natLsl 1 63) 1 = 4611686018427387904
> operand p61*4 (2^63): 9223372036854775808
> intLor (p61*4) 1 = 9223372036854775809
> intLand (p61*4) (p61*4) = 9223372036854775808
> intLxor (p61*8) 1 = 18446744073709551617
> natLor (n61*4) 1 = 9223372036854775809
> natLand (n61*4) (n61*4) = 9223372036854775808
> natLxor (n61*8) 1 = 18446744073709551617
```

So OCaml's reps are 63-bit. Where exactly the targets diverge (corrected
in review round 3): on representable operands, OCaml's `land`, `lor`,
`lxor` and `asr` are EXACT. The primitive divergence is `lsl` past bit 62
(`intLsl 1 63 = 0`; OCaml even yields a NEGATIVE `nat`, `natLsl 1 62`),
plus shifts by at least the word size, where OCaml's result is
unspecified. Measured: `intLsl 1 64 = 1`, and, added in round 3,
`intAsr 5 64 = 5`, `intAsr (0-5) 64 = -5` and `natAsr 5 64 = 5` on OCaml,
where Lean gives `0`, `-1` and `0`. The `land`/`lor`/`lxor` rows of
`p_word_bitwise_wide` only propagate an `lsl`-built operand that already
differs. The `asr`-by-64 rows are pinned in the same probe, in the same
(LP4) class. The disagreement is the 63-bit class ruled on
[USER 2026-09-03], but D2 was given subject to the opposite finding. So
LP4's acceptance went BACK TO THE OPERATOR with this measurement.

**Ruling, 2026-09-30:** [USER 2026-09-30] agreed on points 1-3 of the orchestrator's questions and approved proceeding; question (1): accept
LP4 (unbounded bitwise reps; OCaml wraps at 63 bits) as a registered
OCaml-target deviation under the 2026-09-03 X3 ruling, [USER 2026-09-03]
(OCaml limits hardcoded because of OCaml-level execution issues are forbidden as well; the logical semantics is what counts). LP4 is ACCEPTED. `p_word_bitwise_wide` is registered in
`parity/expected_failures.txt` as class `ruled` (it was `open`); its Lean
pin is unchanged. The same ruling's question (2) keeps the
`p_word_bitwise_wide_mul` runner row (addendum in
`2026-09-03_exception-case-rulings.md`, X3).

**Upstream-Lem candidate** (recorded as D2 asks): the HOL, Isabelle and Coq
meanings of these functions are Lem's own definitions, which are
width-limited through the 31-bit `bitSequence` (`intFromBitSeq`/
`bitSeqFromInt`/`natFromBitSeq`/`bitSeqFromNat`, `resizeBitSeq (Just 31)`).
They therefore differ from the OCaml backend (63-bit) from 2^30 on.

### LP6: mword bit lists were LSB-first on Lean (FIXED)

`mwordFromBitlist`/`mwordToBitlist` treated the head of the list as bit 0.
All of these are MSB-first: Lem's own asserts (`machine_word.lem`
`wordFromBitlist_test`,
`wordFromBitlist [false;false;true;false] : mword ty4 = wordFromNatural 2`,
and `bitlistFromWord_test`), the OCaml reference (`ocaml-lib/lem.ml`
`wordFromBitlist`/`bitlistFromWord`), HOL `v2w`/`w2v` and Isabelle
`of_bl`/`to_bl`. Fix: LemLib `mwordFromBitlist`/`mwordToBitlist` are
MSB-first. A list longer than the width keeps its low bits, as HOL `v2w`
does. Regressions: `p_lib_machine_word`; the `test_mword.lem` asserts
`mw_wordFromBitlist_msb_first` and `mw_bitlistFromWord_msb_first`;
LemLibTest.

### LP7: `word_extract` ignored `hi` on Lean (FIXED)

`mwordExtract lo _hi w` was `BitVec.extractLsb' lo result w` (Isabelle
`Word.slice` semantics). It returned bits beyond `hi` whenever the result
type is wider than `hi-lo+1`: `word_extract 0 3 (0xAB : mword ty8) : mword ty8`
gave 171, where the OCaml reference and HOL (`word_extract hi lo`, then
`w2w`) give 11. Fix: `(BitVec.extractLsb' lo (hi + 1 - lo) w).setWidth result`.
Regressions: `p_lib_machine_word`, the `test_mword.lem` assert
`mw_word_extract_masks_hi`, LemLibTest.

### LP6/LP7 width question: type width or runtime width (OM4: ACCEPTED, ruled OCaml-target deviation, 2026-09-30)

LP6 and LP7 fixed which bits Lean returns. They left one question open:
what is the WIDTH of the result? OCaml's `Lem.mword` carries its width at
run time and takes it from the arguments, whatever the result type says:

- `wordFromBitlist` uses the list length (`ocaml-lib/lem.ml:162`);
- `word_extract` uses `hi-lo+1` (`:138`);
- `word_concat` uses `n1+n2` (`:135`).

LemLib's `mword n` is `BitVec n`, and its width is the TYPE's. Probe
`tests/comprehensive/parity/probes/p_mword_width.lem` measures this. The
runner's diff, verbatim (`<` is OCaml, `>` is Lean):

```
< wordFromBitlist 4 bits at ty8: u=11 len=4 bits=1011
< wordFromBitlist 11 bits at ty8: u=1027 len=11 bits=10000000011
< word_extract 0 3 (171 : ty8) at ty8: u=11 len=4 bits=1011
< word_concat (10 : ty4) (5 : ty4) at ty16: u=165 len=8 bits=10100101
---
> wordFromBitlist 4 bits at ty8: u=11 len=8 bits=00001011
> wordFromBitlist 11 bits at ty8: u=3 len=8 bits=00000011
> word_extract 0 3 (171 : ty8) at ty8: u=11 len=8 bits=00001011
> word_concat (10 : ty4) (5 : ty4) at ty16: u=165 len=16 bits=0000000010100101
```

This is a Lean-vs-OCaml discrepancy. The numeric value agrees whenever
the result type is at least as wide as the runtime width. `word_length`
and `bitlistFromWord` always differ at a mismatched width, and a
too-long bit list gives an out-of-range value on OCaml (1027 in a `ty8`
word). Lean follows the type, as HOL and Isabelle do. [AGENT]
recommendation was to rule it an OCaml-target deviation (a Lem type is a
width, and a `ty8` word of length 4 has no meaning in the prover backends).

**Ruling, 2026-09-30:** [USER 2026-09-30] agreed on points 1-3 of the orchestrator's questions and approved proceeding; question (1): accept
OM4 (mword width from the type; OCaml uses the runtime width) as a
registered OCaml-target deviation under the 2026-09-03 X3 ruling. OM4 is
ACCEPTED. `p_mword_width` is registered as class `ruled` (it was `open`);
its Lean pin is unchanged. The other §2 classes (LP5, OM1–OM3, OM5) are
not covered by this ruling.

### LP8: `chr` succeeded above 255 on Lean (FIXED)

The rep `declare lean target_rep function chr = \`Char.ofNat\`` made
`chr 256` U+0100, where OCaml's `Char.chr` raises
`Invalid_argument "Char.chr"`. Fix: LemLib `lemChr` fails loudly outside
0..255. Bytes 128..255 as Unicode scalars remain the registered F2
strings-are-bytes arc. Regression: failure probe `f_lib_chr_range`.

## 2. Inputs the probes exclude, for an operator ruling

`p_lib_machine_word` pins the OCaml output only where OCaml's `Lem.mword`
implementation agrees with Lem's own definition. Its header
(`tests/comprehensive/parity/probes/p_lib_machine_word.lem:10-19`) names
the input classes it leaves out. Each one is an input where Lean (BitVec)
and OCaml DIFFER, so each needs a ruling (OCaml-target deviation, or a
Lean fix to mirror OCaml). None is registered as ruled. The descriptions
come from the `8ccbe40` record, and the `lem.ml` lines were re-checked
against this branch's `ocaml-lib/lem.ml`:

1. **LP5, `wordToHex` / `show` on an `mword`.** On OCaml it is a stub:
   `machine_word.lem`,
   `let {ocaml;isabelle;coq} wordToHex w = "wordToHex not yet implemented"`.
   The Lean rep is `BitVec.toHex`, so `show` of any machine word differs.
2. **OM1, negation not reduced.** `lem.ml` `word_uminus (n,w) = (n, 2^n - w)`
   gives the out-of-range 2^n for `w = 0`. `uminus`, `wordFromInteger` (at
   every negative multiple of 2^n) and `signedDivide` (at a zero quotient of
   opposite-sign operands) then return 2^n. Lean returns 0.
3. **OM2, `getBit i` reads bits i..2i.** `lem.ml` uses
   `extract_big_int w i (i+1)` (offset i, LENGTH i+1), so `getBit (w8 4) 1`
   is true on OCaml and false on Lean. The two agree only for `i = 0` or
   when bits i+1..2i are clear.
4. **OM3, `setBit` beyond the width.** OCaml ORs in `1 lsl i` without a
   mask, so `setBit (w8 0) 10 true` has value 1024. Lean leaves the word
   unchanged, as HOL does.
5. **OM4, width from the value, not the type** (ACCEPTED 2026-09-30 as a
   ruled OCaml-target deviation, §1). `wordFromBitlist`,
   `word_extract` and `word_concat`, as in §1 above. This one is now
   MEASURED by `p_mword_width`.
6. **OM5, rotations and arithmetic shifts raise.** On OCaml, `word_ror 0`,
   `rotateLeft` by 0 or by the width, `rotateRight` by more than the width,
   and `arithShiftRight` of a negative word by more than the width all raise
   `Invalid_argument` ("Z.extract: …" / "Z.shift_left: …"). Lean rotates
   modulo the width and shifts to all-ones. Here Lean SUCCEEDS where the
   reference FAILS, which the failure-agreement rule forbids unless it is
   ruled.

[AGENT] recommendation (from the `8ccbe40` record, not re-litigated
here): treat OM1–OM5 as OCaml-library bugs, keep Lean on the prover
semantics, and send them upstream. LP5: keep Lean's rendering. These are
the operator's decisions. Until they are made, these classes are
unprobed, known differences, listed here so they are not silent.

**`lnot` at `nat` is not a reachable discrepancy (correction, review round
2).** The round-1 version of this record said that OCaml's `lnot` at `nat`
returns a negative `int` where LemLib's `lemNatLnot` panics. That claim
was not measured, and it is wrong. Measured: a Lem program cannot apply
`lnot` to a `nat` on any target, because the Word library has no
`WordNot nat` instance. `let v (n : nat) : nat = lnot n` is refused by the
type checker with "unsatisfied type class constraint: (Word.WordNot nat)".
The only Lean binding of `lemNatLnot` is `library/transform.lem`, which
does not typecheck ("Type error: unbound variable: find_non_pure") and is
not in the library build, and which has no OCaml rep for `lnot`. So
`lemNatLnot` is dead code. The refusal is pinned by the negative test
`tests/comprehensive/negative/neg_lnot_nat.lem`, so the question comes back
if an instance ever appears. No parity probe is possible.

## 3. Decisions (this branch)

1. **LP4 / D2: DECIDED.** [USER 2026-09-30] agreed on points 1-3 and approved proceeding: LP4 is accepted as a registered
   OCaml-target deviation under the 2026-09-03 X3 ruling
   (`p_word_bitwise_wide`, class `ruled`).
2. **OM4: DECIDED.** Same ruling: accepted as a registered OCaml-target
   deviation under X3 (`p_mword_width`, class `ruled`).
2a. **The `p_word_bitwise_wide_mul` runner row: DECIDED.** Same ruling,
   question (2): the row is kept, reversing X3's "no runner row by design"
   (addendum in `2026-09-03_exception-case-rulings.md`).

Still open:

3. **LP5, OM1, OM2, OM3, OM5** (§2): for each, OCaml-target deviation, or
   mirror OCaml?
4. Whether OM1–OM5, LP5 and the 31-bit prover definitions (LP4) go into
   the upstream Lem report bundle.
5. **`lnot` at `nat`** (§2): not a discrepancy today (unreachable on
   every target, pinned by `neg_lnot_nat`). Decision wanted only on
   housekeeping: delete the dead `lemNatLnot` and the `transform.lem` Lean
   reps, or keep them.
