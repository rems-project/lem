# 04 — OCaml backend: `Assert_extra.fail` applied to an argument prints as `(assert false "msg")`, which is not valid OCaml

Target: `rems-project/lem`, `library/assert_extra.lem` (OCaml target
representation). State: **Draft**, not filed. Drafted 2026-10-03.

## Affected code (upstream `3802cb0`)

`library/assert_extra.lem:27-29`:

```lem
val fail : forall 'a. 'a
let fail = failwith "fail"
declare ocaml target_rep function fail = `assert` `false`
```

lem-lean's copy is the same text at lines 28-30 (it adds a Lean line).

## Classification

**TRUE BUG.** Lem accepts the program, and its OCaml output does not
compile. `fail : forall 'a. 'a` may be instantiated at a function type,
so `fail "message"` type-checks, and the two-token representation
`assert false` is printed without parentheses in application position.

## Reproducer

```lem
open import Pervasives_extra
open import Assert_extra

val pick : nat -> nat
let pick n = if n = 0 then fail "pick: zero" else n
```

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
OCaml 5.4.0; conventions in README §4. With default warning settings
`lem -ocaml` also prints nothing and exits 0. Full transcript:
`repro/failarg/transcript-2026-10-03.txt`.

```
$ lem -wl ign -ocaml failarg.lem
[lem exit 0]
$ ocamlfind ocamlopt -package zarith -linkpkg -I <upstream ocaml-lib> extract.cmxa failarg.ml  -o failarg.exe
File "failarg.ml", line 6, characters 46-58:
6 | let pick n:int=  (if n = 0 then (assert false "pick: zero") else n)
                                                  ^^^^^^^^^^^^
Error: Syntax error: ) expected
File "failarg.ml", line 6, characters 32-33:
6 | let pick n:int=  (if n = 0 then (assert false "pick: zero") else n)
                                    ^
  This ( might be unmatched
[ocamlopt exit 2]
```

## Observed vs expected

Observed: `(assert false "pick: zero")`, a syntax error. Expected: OCaml
that compiles and fails at run time when `n = 0`, e.g.
`((assert false) "pick: zero")`.

## Impact

Easy to hit by accident: with `Assert_extra` opened, an unqualified `fail`
resolves to this function even where the author meant `failwith` or a
module's own `fail : string -> …`. linksem hit it exactly that way. The
error appears only when the generated OCaml is compiled, pointing at
generated code.

## Proposed remedy

1. Parenthesise the representation:
   ``declare ocaml target_rep function fail = `(assert false)` `` (then
   `fail "msg"` prints as `((assert false) "msg")`; checked 2026-10-03 with
   OCaml 5.4.0: it compiles with `Warning 20 [ignored-extra-argument]` and
   raises `Assert_failure` when reached); or have the printer parenthesise a
   multi-token representation in application position, which would fix
   any other such representation too.
2. Optionally warn when `fail` is applied to an argument, since the
   author almost certainly meant `failwith`.

## Origin

linksem (`linksem-lean`), `lean/docs/upstream-tray/lem/01-assert-extra-fail-applied-prints-invalid-ocaml.md`
(branch `lean/port`, commit `9cafe16`, 2026-09-30). That draft stays where
it is, unchanged ([USER 2026-10-03]: the tray lives in lem-lean and the copies stay); this draft is
based on it. Its reproducer was run on upstream `f5529b2`, an ancestor of
`3802cb0` with an identical `assert_extra.lem`; the output above is a
fresh run on `3802cb0`, and its compiler error is the same as the one
recorded there.

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
