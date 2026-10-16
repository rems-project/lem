# 13 — OCaml target: `=` on a user type that contains a set or map raises `Invalid_argument "compare: functional value"`

Target: `rems-project/lem`, OCaml backend / `ocaml-lib` (`Pset`, `Pmap`)
and `library/basic_classes.lem`. State: **Draft**, not filed. Drafted
2026-10-03.

## Affected code (upstream `3802cb0`)

- The `Eq` class's default instance is `unsafe_structural_equality`
  (`library/basic_classes.lem:70-71`), represented on OCaml as `infix =`
  (`:58`). The comment above it (`:44-53`) warns that structural equality
  "differs significantly for each backend" and that "OCaml can`t check
  equality of function types".
- On OCaml a Lem `set` is a record holding its comparator closure:
  `type 'a set = { cmp : 'a -> 'a -> int; s : 'a rep }`
  (`ocaml-lib/pset.ml:299`); a `map` likewise
  (`ocaml-lib/pmap.ml:280`).
- Lem's own set equality is comparator-keyed: `setEqual` is `Pset.equal`
  (`library/set.lem:54`, `ocaml-lib/pset.ml:325`), used by
  `instance Eq (set 'a)` (`library/set.lem:57`).

So any record or variant type with a set or map field and no `Eq`
instance of its own is compared with OCaml's polymorphic `=`, which
raises on the closure. `ocaml-lib/pset.ml` and `pmap.ml` in lem-lean are
byte-identical to upstream's; lem-lean's `basic_classes.lem` has the same
lines at 60 and 74-75.

## Classification

**KNOWN LIMITATION / question.** The `unsafe_` name and its comment show
that the authors know structural equality can fail on OCaml; what may
not be expected is that an ordinary set-valued field is enough to trigger
it, and that nothing warns at generation time. Lem's semantics (and its
HOL4/Isabelle/Coq targets) give these comparisons a value. Whether to fix
or to document is the Lem authors' call.

## Reproducer

```lem
open import Pervasives

type config = <| label : nat; members : set nat |>

let c1 : config = <| label = 1; members = {1; 2; 3} |>
let c2 : config = <| label = 1; members = {3; 2; 1} |>

let members_same () : bool = (c1.members = c2.members)
let same () : bool = (c1 = c2)
let refl () : bool = (c1 = c1)
```

Generated OCaml (verbatim): `let same () : bool=  (c1 = c2)`,
`let members_same () : bool=  ( Pset.equal c1.members c2.members)`. The
driver (`repro/x1/main.ml`) calls each thunk and reports an exception.

## Verbatim output

Captured 2026-10-03, upstream Lem `3802cb0` (`lem -v`: `Lem 3802cb0`),
upstream `ocaml-lib` compiled from the same checkout, OCaml 5.4.0,
zarith 1.14; conventions in README §4. With default warning settings
`lem -ocaml` also prints nothing and exits 0. Full transcript:
`repro/x1/transcript-2026-10-03.txt`.

```
$ lem -wl ign -ocaml x1.lem
[lem exit 0]
$ ocamlfind ocamlopt -package zarith -linkpkg -I <upstream ocaml-lib> extract.cmxa x1.ml main.ml -o x1.exe
[ocamlopt exit 0]
$ ./x1.exe
members_same = true
same raises Invalid_argument("compare: functional value")
refl raises Invalid_argument("compare: functional value")
[run exit 0]
```

## Observed vs expected

Observed: `same` and even `refl` (`c1 = c1`) raise; `members_same` is
`true`. Expected per Lem's semantics: all three `true`.

## Impact

A specification that puts a set or map inside a record or variant and
compares such values (directly, or through a containing type's default
equality, `elem`, list equality, …) compiles cleanly and fails at run time
on OCaml only.

## Proposed remedies (for the Lem authors to choose among)

1. Document it at `unsafe_structural_equality` and in the OCaml backend
   section of the manual: structural `=` is undefined on values containing
   sets or maps; define an `Eq` instance (using `setEqual`/`mapEqual` on
   the fields) for such types.
2. Warn at generation time when the default `Eq` instance is used at a
   type that contains `set` or `map`.
3. Derive `Eq`/`Ord` for user record and variant types on OCaml from
   their components instead of falling back to polymorphic `=`.
4. Make the OCaml representation closure-free so that polymorphic
   comparison works; the largest change.

## Origin

- Cerberus (`cerberus-lean`) `lean_frontend/docs/upstream-tray/lem/01-polymorphic-compare-on-set-values.md`
  (mainline `mdd/cerberus-lean`, added in commit `56ab39ea0`, drafted
  2026-09-03). That draft stays where it is, unchanged
  ([USER 2026-10-03]: the tray lives in lem-lean and the copies stay); this draft is based on its
  text and reproducer. Its "Verbatim output" section was never filled in
  ("Not executed in the slice that drafted this report"); the run above
  is the first execution, and it confirms that draft's expectation,
  including that reflexive equality raises.
- lem-lean `doc/lean-backend/2026-09-03_parity-fix-record.md` §2 row X1
  ("reading; not probed") and `doc/lean-backend/2026-09-03_exception-case-rulings.md`
  §2 X1; ruling recorded in the parity-fix record §4: RULED 2026-09-03
  ([USER] agreed as regards lem): X1 and X3/N4 are recorded as OCaml-backend
  deviations from lem's own prover-side semantics.

## Provenance

Found and analysed by AI agents (Claude, Anthropic) working under the
direction and review of a human operator. Any filed issue must say so
(INDEX.md, "Provenance labelling").
