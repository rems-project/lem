# 22 — Note: `nat` and `int` are 63-bit and wrap silently on OCaml, unbounded on the provers (a `nat` can become negative)

Target: `rems-project/lem`, `library/num.lem` (documentation / OCaml
target). State: **Draft**, not filed. Drafted 2026-10-03. This is a note
for the record and a documentation suggestion, not a defect report.

## Affected code (upstream `3802cb0`)

`library/num.lem:101-115`:

```lem
(* bounded size natural numbers, i.e. positive integers *)

(* "nat" is the old type "num". It represents natural numbers. 
   These numbers might be bounded, however no checks of the boundedness are
   provided. The theorem prover backends map nat to unbounded size 
   natural numbers. However, OCaml uses the type "int", which is bounded.
   Using "int" allows using many functions like "List.length" without wrappers.
   This leeds to nice readable code, but a slightly fuzzy concept what
   "nat" represents. If you want to use unbounded natural numbers, use "natural"
   instead. *)

declare hol      target_rep type nat = `num` 
declare isabelle target_rep type nat = `nat` 
declare coq      target_rep type nat = `nat`  
declare ocaml    target_rep type nat = `int` 
```

and `int` (`:135-141`): "bounded size integers with uncertain length",
OCaml `int`, provers `int`/`Z`. `natAdd` is OCaml `+` (`:294`).
lem-lean's copy keeps this text (lines 102-117).

## Classification

**INTENDED GAP** (documented design choice). Reported only as a note,
with two observations the comment does not spell out: on OCaml the wrap is
silent (no check, as the comment says) and a `nat` can become negative,
which no prover model of `nat` admits.

## Reproducer

```lem
open import Pervasives

let max_nat_ocaml : nat = 4611686018427387903   (* 2^62 - 1 *)
let wrapped : nat = max_nat_ocaml + 1
let wrapped_is_zero_or_more : bool = (wrapped >= 0)
let pow_wrap : nat = 2 ** 64
let int_wrap : int = (4611686018427387903 : int) + 1
```

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
upstream `ocaml-lib` compiled from the same checkout, OCaml 5.4.0,
zarith 1.14; conventions in README §4. Full transcript
(`repro/nat63/transcript-2026-10-03.txt`):

```
$ lem -wl ign -ocaml nat63.lem
[lem exit 0]
$ ocamlfind ocamlopt -package zarith -linkpkg -I <upstream ocaml-lib> extract.cmxa nat63.ml main.ml -o nat63.exe
[ocamlopt exit 0]
$ ./nat63.exe
wrapped = -4611686018427387904
wrapped >= 0 = false
2 ** 64 = 0
int_wrap = -4611686018427387904
[run exit 0]
```

## Observed vs expected

On OCaml: `(2^62 - 1) + 1` at `nat` is `-2^62`, and `wrapped >= 0` is
false; `2 ** 64` at `nat` is `0`. On the prover targets the same
definitions denote `2^62` (and `true`) and `2^64`.

## Impact

Lem developments whose `nat`/`int` values can exceed `2^62` (byte
counts, addresses, 64-bit quantities) compute different results on OCaml
and on the provers, without a diagnostic. The usual remedy — use
`natural`/`integer` — is in the comment; what is missing is that the
comment does not say the wrap is silent and can produce negative `nat`s.

## Suggestions (for the Lem authors)

1. Extend the comment (and the manual's OCaml section) with the two
   observations above.
2. Optionally, checked conversions at the boundaries (`natFromNatural`,
   `natFromInteger`, numerals above `2^62`) that fail rather than wrap.

## Origin

- Cerberus (`cerberus-lean`) `lean_frontend/docs/upstream-tray/lem/README.md`:
  "One note that is deliberately *not* a report: Lem's `nat` and `int` are
  63-bit machine integers on the OCaml target, by documented upstream
  choice (`library/num.lem`, the comment on `nat`), while the
  theorem-prover targets map them to unbounded numbers".
- lem-lean `doc/lean-backend/2026-09-03_exception-case-rulings.md` §2 "X3 /
  N4"; the ruling recorded in `2026-09-03_parity-fix-record.md` §4:
  RULED 2026-09-03 ([USER] agreed as regards lem): X1 and X3/N4 are recorded as
  OCaml-backend deviations from lem's own prover-side semantics. The
  [AGENT] answer put to the operator there called it "a documented design
  compromise in upstream lem, not a bug".
- Drafted here because the [USER 2026-10-03] ruling (all 16 findings, re-verified) asks for a
  draft for every finding; filed as a note, if at all.

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
