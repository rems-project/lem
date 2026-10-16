# 01 — Block-formatted output is decoded as Latin-1: non-ASCII text in Lem-generated code is encoded twice (OCaml string literals change value)

Target: `rems-project/lem`, `src/output.ml` (all backends that format
blocks; the value change is on OCaml). State: **Draft**, not filed.
Drafted 2026-10-03.

No patch branch. A one-line fix (below) was built and checked on a local
branch on `3802cb0`; that branch was deleted, as this tray prepares
reports only, not pull requests ([USER 2026-10-03] ruled out upstream-PR writing and had the branches deleted).

## Affected code (upstream `3802cb0`)

- `src/output.ml:409-449`, `to_rope_help_block`: each piece of the block
  is printed into `Format.str_formatter` as UTF-8
  (`Format.pp_print_string Format.str_formatter (Ulib.Text.to_string
  res)`, `:432`), and the formatted string is read back with `r s`
  (`:448`), where `r` is `Ulib.Text.of_latin1` (`:58`).
- Blocks are formatted (the `true` argument of `block`/`block_hov`) for
  expressions Lem introduced itself (`Typed_ast_syntax.is_pp_exp`, which
  tests for an `Ast.Trans (true, …)` location): `src/backend.ml:2261,2291`,
  `src/coq_backend.ml:827,869,927,947-951`. Pattern compilation produces
  such expressions.

lem-lean's `src/output.ml` differs: its line 473 already decodes with
`Ulib.Text.of_string` (fork commit `c515e6d`, 2026-03-06).

## Classification

**TRUE BUG.** The two halves of one function disagree on the encoding:
the pieces are written as UTF-8 and read back as Latin-1. Lem requires
string literals to be valid UTF-8 (`src/lexer.mll:285-289`), and outside
a formatted block the same literal is printed correctly, so the
double encoding is not a design choice.

## Reproducer

```lem
open import Pervasives

let g (n : nat) : string =
  match n with
    | 0 -> "§zero"
    | m + 1 -> "§succ"
  end
```

(`blk.lem`; the `§` is UTF-8 `c2 a7`.) Driver `main.ml`:

```ocaml
let () = Printf.printf "String.length (g 0) = %d (source literal is 6 bytes)\n" (String.length (Blk.g 0))
```

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
OCaml 5.4.0; conventions in README §4.

`lem -wl ign -<t> -outdir out blk.lem` for `t` in `ocaml hol isa coq`
(each exit 0), then `grep -n '§\|Â\|zero\|succ' out/*` (full transcript:
`repro/blk/transcript-2026-10-03.txt`):

```
out/blk.ml:5:  (if(n = 0) then "Â§zero" else "Â§succ")
out/blkScript.sml:16:      0 => "\194\167zero"
out/blkScript.sml:17:    |  (SUC m) => "\194\167succ"
out/blk.v:20:    | 0%nat => "§zero"
out/blk.v:21:    | S (m) => "§succ"
```

Bytes of `blk.ml` line 5 (`xxd`):

```
00000000: 2020 2869 6628 6e20 3d20 3029 2074 6865    (if(n = 0) the
00000010: 6e20 22c3 82c2 a77a 6572 6f22 2065 6c73  n "....zero" els
00000020: 6520 22c3 82c2 a773 7563 6322 290a       e "....succ").
```

Compiled against upstream's OCaml library and run:

```
String.length (g 0) = 8 (source literal is 6 bytes)
```

With that fix applied, `lem` printed the OCaml line
`(if(n = 0) then "§zero" else "§succ")`, the program prints
`String.length (g 0) = 6 (source literal is 6 bytes)`, and the HOL4,
Isabelle and Coq output for this file is byte-identical to `3802cb0`'s.

## Observed vs expected

Observed: on OCaml, `g 0` is the 8-byte string `"Â§zero"`. Expected: the
6-byte string written in the source, as for a literal outside a compiled
match (`let s : string = "§"` prints as `"§"`; draft 02's reproducer shows
it).

## Impact

A silent change of string values on the OCaml target, only in code that
Lem rewrote (compiled patterns, and on Coq the other `is_pp_exp` sites).
Any non-ASCII text that reaches a formatted block is affected the same
way. The library itself is ASCII at those sites (the patch leaves all 145
generated library files byte-identical).

## Proposed remedy

`src/output.ml:448`: `([], Ulib.Text.of_string s, (0, Kwd s, Kwd s))`.
This line is the whole fix.

## Origin

- lem-lean commit `c515e6d` (2026-03-06, "Fix UTF-8 double-encoding,
  constructor scoping, and whitespace in Lean backend") made this change
  inside a Lean-backend commit.
- lem-lean `doc/lean-backend/2026-08-31_backend-quality-review.md` m3(c)
  recorded it as an unflagged shared-code fix: "`src/output.ml:470` —
  `to_rope`'s block-format path decodes UTF-8 where upstream decoded
  latin1 (an unflagged fix; changes bytes wherever non-ASCII flows through
  isa/hol block formatting)". That review is [AGENT] work.
- The upstream reproducer above is new in this tray (2026-10-03, [AGENT]).

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say
so (INDEX.md, "Provenance labelling").
