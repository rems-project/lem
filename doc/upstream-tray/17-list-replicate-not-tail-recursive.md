# 17 — OCaml: `List.replicate` is not tail-recursive and overflows the stack on long lists

Target: `rems-project/lem`, `library/list.lem` (the OCaml library module
`Lem_list` is generated from it). State: **Draft**, not filed. Drafted
2026-10-03.

## Affected code (upstream `3802cb0`)

`library/list.lem:593-599`:

```lem
val replicate : forall 'a. nat -> 'a -> list 'a
let rec replicate n x =
  match n with
    | 0 -> []
    | n' + 1 -> x :: replicate n' x
  end
declare termination_argument replicate = automatic
```

Isabelle and HOL4 have target representations (`:601-602`); OCaml uses
the definition, generated as `ocaml-lib/lem_list.ml:345-348` (a generated,
untracked file):

```ocaml
let rec replicate n x:'a list= 
  (
  if(n = 0) then ([]) else
    (let n'0 =(Nat_num.nat_monus n 1) in x :: replicate n'0 x))
```

One stack frame per element. lem-lean's `list.lem` has the same
definition (at lines 612-618); the generated `lem_list.ml` line cited in
the Cerberus record (`:341`) is the fork's numbering.

## Classification

**TRUE BUG** (robustness). The function's result is correct, but its
stack use is linear in the length, so on a bounded stack it fails on
lengths that a library `replicate` is expected to handle. OCaml's
`List.init` handles the same length under the same bound.

## Reproducer

```lem
open import Pervasives

let rl (n : nat) : nat = length (replicate n (0 : nat))
```

Driver: `Printf.printf "replicate n=%d  length=%d\n%!" n (Replicate.rl n)`
with `n` from the command line (`repro/replicate/`). The control is
`List.init n (fun _ -> 0)` compiled the same way (`control.ml`). OCaml 5
grows the stack on demand up to the `l` limit of `OCAMLRUNPARAM` (in
words; the switch's `caml/config.h` has `#define Max_stack_def (128 *
1024 * 1024)`), so the run sets `l=1M` (one million words, 8 MiB on
64-bit) to show the failure at a modest size.

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
upstream `ocaml-lib` compiled from the same checkout (with `-g`), OCaml
5.4.0; conventions in README §4. Full transcript
(`repro/replicate/transcript-2026-10-03.txt`), after the build lines and
a run at the default `n = 1000`:

```
$ OCAMLRUNPARAM=l=1M ./replicate.exe 1000000
Fatal error: exception Stack overflow
[exit 2]
$ OCAMLRUNPARAM=l=1M ./replicate.exe 10000000
Fatal error: exception Stack overflow
[exit 2]
$ OCAMLRUNPARAM=b,l=1M ./replicate.exe 1000000 | head -8
Fatal error: exception Stack overflow
Raised by primitive operation at Lem_list.replicate in file "lem_list.ml", line 348, characters 46-61
Called from Lem_list.replicate in file "lem_list.ml", line 348, characters 46-61
Called from Lem_list.replicate in file "lem_list.ml", line 348, characters 46-61
Called from Lem_list.replicate in file "lem_list.ml", line 348, characters 46-61
Called from Lem_list.replicate in file "lem_list.ml", line 348, characters 46-61
Called from Lem_list.replicate in file "lem_list.ml", line 348, characters 46-61
Called from Lem_list.replicate in file "lem_list.ml", line 348, characters 46-61
$ OCAMLRUNPARAM=l=1M ./control.exe 1000000
List.init n=1000000  length=1000000
[exit 0]
$ /usr/bin/time -f '%e s %M kB' ./replicate.exe 10000000
replicate n=10000000  length=10000000
3.84 s 396016 kB
[exit 0]
```

The last run uses the default limit: `replicate` completes at 10 million
elements there.

## Observed vs expected

Observed: `Stack overflow` at one million elements under an 8 MiB stack
limit, where `List.init` succeeds. Expected: constant stack use.

## Impact

Programs generated from Lem that build long lists with `replicate` (e.g.
zero-initialising large memory models) die with `Stack overflow` wherever
the stack is bounded below what the list length needs (a lowered `l`, or
a runtime or thread that runs on a fixed-size stack). The Cerberus project saw its
OCaml oracle's loud overflow site at `Lem_list.replicate` on large static
arrays in a bounded-stack configuration.

## Proposed remedy

An OCaml target representation for `replicate`, e.g.
``declare ocaml target_rep function replicate n x = `List.init` n (fun _ -> x)``
(or a tail-recursive helper in `ocaml-lib`), keeping the Lem definition
for the provers. Checked 2026-10-03 on the same build with the definition
and this declaration copied into a user file under another name
(`myReplicate`): Lem emits `List.init n (fun _ -> (0 : int))`, and the
program completes one million elements under `OCAMLRUNPARAM=l=1M` (exit
0). `List.init` raises `Invalid_argument` for a negative length, which an
OCaml `nat` can be after wrap-around (draft 22); the current definition
returns a one-element list there (by reading the generated code), so the two differ on that input.

## Origin

Cerberus (`cerberus-lean`) `lean_frontend/docs/2026-09-01_mem-scale-design.md`
(mainline `mdd/cerberus-lean`), lines 340-343: "Separate, not blocking,
lem-side: the ORACLE's own loud overflow site is `Lem_list.replicate` in
lem's OCaml runtime library (`lem-lean/ocaml-lib/lem_list.ml:341`,
non-tail `replicate`) — an upstream-lem note for the tray, since the
oracle currently completes the 10 M case at the default stack." The same
record set's tray draft 18 (Cerberus tray, monadic list combinators)
mentions the `Lem_list.replicate` backtrace. These are [AGENT] records;
the reproducer above is new in this tray (2026-10-03, [AGENT]).

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
