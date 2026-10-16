# 14 — OCaml backend: `Function_extra.THE` is represented as `THE`, which does not exist in OCaml; generated code does not compile

Target: `rems-project/lem`, `library/function_extra.lem` (OCaml target
representation). State: **Draft**, not filed. Drafted 2026-10-03.

## Affected code (upstream `3802cb0`)

`library/function_extra.lem:36-39`:

```lem
val THE : forall 'a. ('a -> bool) -> maybe 'a
declare hol      target_rep function THE = `$THE`
declare ocaml    target_rep function THE = `THE`
declare isabelle target_rep function THE = `The_opt`
```

There is no OCaml value or constructor `THE` in `ocaml-lib` (the generated
`ocaml-lib/lem_function_extra.ml` contains only the `val` comment). lem-lean's
copy has the same lines at 36-39 plus a Lean line.

## Classification

**TRUE BUG** (minor). `THE` (definite choice) is not computable in
general, so a missing OCaml implementation is reasonable; but the
declaration makes Lem accept a use and emit OCaml that refers to a
non-existent name, instead of refusing at generation time.

## Reproducer

```lem
open import Pervasives_extra
open import Function_extra

let pick () : maybe nat = THE (fun (x : nat) -> x = 3)
```

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
upstream `ocaml-lib` compiled from the same checkout, OCaml 5.4.0;
conventions in README §4. With default warning settings `lem -ocaml` also
prints nothing and exits 0. Full transcript:
`repro/the/transcript-2026-10-03.txt`.

```
$ lem -wl ign -ocaml the.lem
[lem exit 0]
$ ocamlfind ocamlopt -package zarith -linkpkg -I <upstream ocaml-lib> extract.cmxa the.ml  -o the.exe
File "the.ml", line 5, characters 29-32:
5 | let pick () :  int option=  (THE (fun (x : int) -> x = 3))
                                 ^^^
Error: This variant expression is expected to have type int option
       There is no constructor THE within type option
[ocamlopt exit 2]
```

## Observed vs expected

Observed: Lem exits 0; the OCaml does not compile, with an error about a
constructor. Expected: either a generation-time error, as Lem gives for
other functions without an implementation on a target, or an OCaml
function that fails at run time with a clear message. For comparison
(same build, same date), a `val foo : nat -> nat` with no definition, used
in `let bar (n : nat) : nat = foo n`, gives at generation time
(`repro/the/norep.lem`, `repro/the/transcript-norep-2026-10-03.txt`):

```
File "norep.lem", line 5, character 27 to line 5, character 29
  Type error: unbound variable for targets {ocaml}: foo
[exit 1]
```

## Impact

Small: `THE` is rarely executable in practice. The cost is a confusing
OCaml error pointing at generated code.

## Proposed remedy

Remove the OCaml `target_rep` line, so that Lem reports the missing
implementation at generation time (if the library build needs a
definition, `let {ocaml} THE _ = failwith "THE is not executable"`).

## Origin

lem-lean library-parity work: archived record only (lem-lean commit
`8ccbe40`, branch `archive/linksem-fixes-2026-09-30` of the linksem
checkout, `doc/lean-backend/2026-09-30_library-parity-coverage.md` §2 "THE
— no OCaml implementation (QUESTION, not probed)": "no such OCaml value
exists (`p_zz_the`: "There is no constructor THE within type option" — the
OCaml build fails)"). Also recorded as row X5 of lem-lean
`doc/lean-backend/2026-09-03_parity-fix-record.md` ("no OCaml definition
(comment only)"). Both are [AGENT] work; the tray scope is
the [USER 2026-10-03] ruling (all 16 findings, re-verified).

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
