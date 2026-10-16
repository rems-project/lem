# String representation design — lem `string`/`char` as BYTES on the Lean target (F2)

Provenance: parity-fix slice 2026-09-03 (branch `arc/lem-parity`), design
note commissioned by the slice brief ("F2 — DESIGN ONLY in this slice");
scope-status under the [USER 2026-09-03] zero-discrepancy ruling: F2 is a
BUG to fix (its L price is not an exception argument), implemented as the
LAST slice of the arc after the S/M fixes land, unless this note surfaces
a compelling impossibility (it does not; it surfaces a price). Judgments
are [AGENT] unless marked. Measured outputs are quoted verbatim from
`tests/comprehensive/parity/expected/p_str_bytes.out` (the OCaml
reference) and the noodle record's diff.

## 1. The discrepancy

The noodle probe `p_str_bytes.lem` (now `tests/comprehensive/parity/probes/`)
prints, on the OCaml reference (verbatim pin):

```
len e-acute: 2
len mixed: 7
explode count e-acute: 2
explode ords e-acute: [195; 169]
chr 200 implode: <the single raw byte 0xC8>
nth 1 of e-acute+x: 169
```

and on the Lean target (verbatim, noodle record):

```
len e-acute: 1
len mixed: 4
explode count e-acute: 1
explode ords e-acute: [233]
chr 200 implode: È
nth 1 of e-acute+x: 120
```

`p_str_escapes.lem` line 14: `unicode literal: [206; 187]` vs `[955]`.
Every other string/char row of both probes is byte-identical (ASCII).

## 2. The OCaml semantics (the reference)

lem `string` is OCaml `string` (`library/string.lem:26`), lem `char` is
OCaml `char` (`:21`) — a string is a SEQUENCE OF BYTES, a char is a byte.

| lem function | OCaml rep (library/*.lem) | byte semantics |
|---|---|---|
| `toCharList` | `Xstring.explode` (ocaml-lib/xstring.ml:1) | one `char` per BYTE, `s.[i]` |
| `toString` | `Xstring.implode` | `Bytes.set` per char: any byte sequence, valid UTF-8 or not |
| `stringLength` | `String.length` | byte count |
| `String_extra.nth` | `String.get` | byte at index; `Invalid_argument "index out of bounds"` otherwise |
| `String_extra.ord` | `Char.code` | 0..255 |
| `String_extra.chr` | `Char.chr` | byte; `Invalid_argument "Char.chr"` for n > 255 |
| `makeString n c` | `String.make` | n copies of the byte |
| `(^)` / `concat` / `stringConcat` | `^` / `String.concat` | byte concatenation |
| `stringEquality`, `stringCompare` | `=` / `compare` | bytewise (unsigned) lexicographic |
| `string_case` / `cons_string` | `Xstring.string_case` (`String.get s 0`, `String.sub s 1`) / `String.make 1 c ^ s` | byte split |
| `show` (string) | `Show.stringFromString` (lem def: `"\"" ^ s ^ "\""`, escapes via lem def over `toCharList`) | bytes |
| literals `"é"` | OCaml literal | the source file's UTF-8 BYTES (lem's lexer requires valid UTF-8 input, so literals are always valid UTF-8 byte strings; `chr` is the only way to build a non-UTF-8 byte string) |

Every byte value 0..255 is a legal `char`; every byte sequence is a legal
`string`.

## 3. The Lean semantics today

`string = String` (`string.lem:27`), `char = Char` (`:22`). Lean's
`String` is a UTF-8 encoded sequence of Unicode SCALAR VALUES with the
invariant that the encoding is valid; `Char` is a scalar value (`UInt32`
with a validity proof). `String.length` counts scalars; `toList` yields
scalars; `Char.ofNat 200` is U+00C8 which ENCODES as two bytes; a byte
sequence that is not valid UTF-8 (e.g. the lone byte 0xC8 the OCaml
`chr 200 implode` produces) is NOT REPRESENTABLE as a Lean `String` at
all. `Char.ofNat n` for n > 255 yields a scalar (or U+0000 for invalid
code points) where OCaml raises.

Consequence: no re-mapping of the operations on Lean's `String` can be
faithful — option (B) below is impossible, not merely expensive.

## 4. Options

### (A) A byte-string type in LemLib, all reps redirected — RECOMMENDED

```lean
structure LemString where bytes : ByteArray   -- lem `string`
abbrev LemChar := UInt8                         -- lem `char`
```

- Reps: `toCharList = fun s => s.bytes.toList`, `toString = ⟨ByteArray.mk ∘ List.toArray⟩`,
  `stringLength = bytes.size`, `nth = bytes.get!` (failwithI on out of
  range — `Invalid_argument`), `ord = UInt8.toNat`, `chr = fun n => if n < 256
  then UInt8.ofNat n else failwithI "Char.chr"`, `makeString`, `(^)` =
  `ByteArray.append`, `concat`/`stringConcat` = the tail-recursive join,
  equality/compare = bytewise (`ByteArray` has no `Ord`; a loop), `string_case`,
  `cons_string`, `Show` instances (`stringFromString`, `stringFromChar`
  escapes — currently lem defs over `toCharList`, so they follow automatically),
  `stringFromNat/Int/Integer` (lem defs producing char lists — follow),
  `naturalOfString`/`integerOfString` (parse bytes).
- Literals: the backend's string-literal emission changes from `"…"` to
  `(LemString.ofString "…")` — the UTF-8 bytes of the Lean literal ARE the
  OCaml literal's bytes, since lem's lexer only admits valid UTF-8 (a
  kernel-transparent def; a `Coe String LemString` would hide the seam,
  so an explicit constructor is preferred). Char literals `'c'` become
  `(‹byte› : UInt8)`; the existing `lean_char_escape` (which today maps
  bytes 0x80-0xFF to Latin-1 scalars, `src/lean_backend.ml:125-140`)
  emits the byte value instead.
- Pattern matching on string literals (lem `match s with "abc" -> …`)
  goes through `string_case`/`cons_string` pattern reps or literal
  patterns; literal patterns on `LemString` need `DecidableEq`
  (`ByteArray` has `BEq`; derive `DecidableEq` on the structure via a
  `decEq` on `toList`) — verify in the suite (`test_strings_chars.lem`).
- `Inhabited`, `BEq`, `Ord`, `Hashable`, `Repr` instances on `LemString`;
  `Ord` bytewise unsigned like OCaml's `compare` on strings.
- Interop with the host: `LemString.toString? : LemString → Option String`
  (valid UTF-8 only) and `LemString.toStringLossy`; for OUTPUT the
  consumer writes the bytes (`IO.FS.Stream.write`) so non-UTF-8 bytes
  reach stdout exactly as OCaml's `print_string` does.

### (B) Keep Lean `String`, re-map the operations to bytes — IMPOSSIBLE

`stringLength = utf8ByteSize` and `toCharList = utf8 bytes as Latin-1
chars` are expressible, but `toString` (implode) of an arbitrary byte
list — in particular `chr 200 implode`, and every byte string built
from `chr` — has no `String` value (invalid UTF-8 is not a `String`).
Rejected on faithfulness, not price.

### (D) Runtime refusal of non-ASCII (fallback, EXCEPTION-CASE argument only)

Keep `String`; make `chr n` for n ≥ 128 and any non-ASCII literal a loud
`failwithI` ("byte strings unsupported on the Lean target"). This is a
"missing feature" refusal, but at RUNTIME, not generation time — the
[USER 2026-09-03] missing-feature allowance is for generation-time
refusals; non-ASCII literals COULD be refused at generation time (the
backend sees them) but `chr`'s argument is runtime data. Offered only as
the fallback if the operator declines the L price; it would be an
EXCEPTION-CASE for the operator to accept, not an [AGENT] decision.

## 5. Consumer impact (cerberus-lean)

- Every generated string literal changes shape (`"x"` →
  `LemString.ofString "x"`): the whole generated tree moves textually;
  semantics preserved for ASCII (all of cerberus's literal strings).
- Hand-written seams taking generated strings as Lean `String` break at
  compile time (LOUD): `CerbPP.lean` (the pretty printer consumes
  generated `String`s), `CoreParser.lean` (`String.mk`, `String.singleton`
  at :70, :662), `CabsImport.lean`/`CerbDecode.lean` (C-source and
  literal decoding), `CerbUtils.lean:94` (`Char.ofNat (Int.emod n 256).toNat`
  — a BYTE-to-char conversion that is exactly the Latin-1 workaround the
  new representation makes unnecessary), `Main.lean` (stdout). Each
  needs a conversion at the boundary; the byte-faithful output path
  (write bytes) replaces `IO.println` on generated strings.
- Model-side uses that become byte-correct: `core_run_effect.lem:51`
  (`stringLength` as a comparator tie-break — today lengths differ from
  OCaml for non-ASCII), `formatted.lem:91,98` (`ord c - 48` digit
  parsing; ASCII, unchanged), `driver.lem:1658,1771` (`toCharList` of
  command-line argument strings — non-ASCII arguments become bytes as
  on OCaml).
- Differential battery: byte-identity of outputs currently holds for
  ASCII; the change is TOWARD the oracle for any non-ASCII byte that
  reaches a lem string (C string literals with UTF-8 or `\x` escapes,
  identifiers with non-ASCII characters, file names).
- Native externs: none touch lem strings (`native/*.c`: `lean_box(0)`
  maps, a counter, md5 over `ByteArray`? — `md5.c` takes a Lean
  `ByteArray`/`String` argument: check its signature at implementation
  time; if it takes a `String`, it changes to `LemString.bytes`).

## 6. Two-target parity tests that gate it

- `p_str_bytes.lem`, `p_str_escapes.lem` (existing pins, currently RED
  on 6 + 1 rows) — must go GREEN.
- New `p_str_ops.lem`: every function of §2 over ASCII, Latin-1 bytes
  (via `chr`), multi-byte UTF-8 literals, empty strings, `nth` in
  range, `compare` orderings across the 0x7F/0x80 boundary
  (unsigned bytewise), `show` of a byte string, `stringFromNat` etc.
- New failure probes: `f_chr_range.lem` (`chr 256`: OCaml
  `Invalid_argument "Char.chr"`), `f_string_nth_oob.lem` (`nth "ab" 5`:
  `Invalid_argument "index out of bounds"`), both must fail on both
  targets after printing the same prefix.
- Output byte-identity: a probe whose reference prints a raw non-UTF-8
  byte (`chr 200`) — the runner diffs stdout bytes, so the Lean binary
  must write the byte, not its UTF-8 encoding (this is the §4(A)
  output-path requirement, tested end to end).
- Suite: `test_strings_chars.lem` asserts (byte lengths, ords) and the
  string-literal pattern-matching cases must keep passing.

## 7. Price and slice plan

Price: **L** (the brief's estimate stands): LemLib string module +
instances (~300 lines, S/M), backend literal/char emission and the
`lean_char_escape` rework (S), library reps in `string.lem`,
`string_extra.lem`, `show.lem`, `num_extra.lem` (S), suite: parity
probes + failure probes + `test_strings_chars` (S), cerberus consumer
seams — CerbPP/CoreParser/CabsImport/CerbDecode/CerbUtils/Main
conversions and the byte output path (M, cerberus-side slice), full
differential re-gate (cerberus-side).

Slice plan (after the S/M fixes of this arc are merged):

1. LemLib `LemString`/`LemChar` + instances + the §2 reps as LemLib
   defs; `lake build` green; kernel-checked examples of the byte
   observables (`#guard`s) in LemLibTest.
2. Backend: literal emission + char escapes; `tests/comprehensive`
   generate+compile green; `-lem` identity echo unaffected (literals are
   re-rendered from the source text, not from the Lean rep).
3. Library reps redirected; the F2 parity probes and failure probes
   green; `nonlean-regress` byte-identical (all changes are Lean-scoped
   declares).
4. Record + DESIGN.md (the "strings are bytes" statement) + manual.
5. Cerberus-side slice (separate): seams, byte output path, pin bump,
   differential re-gate.

No impossibility surfaced; the only genuine constraint is that option
(B) cannot work, which forces the representation change of (A).
