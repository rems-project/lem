# Runtime provenance and notices

Checked 2026-09-25 against Lem implementation `fd048dbaeed9e0031496aa6ae4a56bb20c07841a`
after M8 notice restoration. This records source provenance;
it does not grant a new license or claim a legal review.

`LemLib.lean` contains Lean translations of the AVL set/map algorithms in
`ocaml-lib/pset.ml` and `ocaml-lib/pmap.ml`, inside the `Pset` and `Pmap`
namespaces. Their headers identify Xavier Leroy and copyright 1996 INRIA;
the Lem modifications are credited to Scott Owens (sets, 2010-10-28) and
Susmit Sarkar (maps, 2010-11-30). Those headers are retained verbatim in
`LemLib.lean`. The Lean implementations adapt the representation and
termination arguments, so “verbatim ports” was not a precise description.

The root [LICENSE](../LICENSE) assigns the OCaml source files the GNU
Library General Public License, Version 2, and includes its full text.
The translated portions retain those terms. The linking exception referenced
by their original headers is now reproduced there from the
[OCaml 3.12.0 LICENSE](https://github.com/ocaml/ocaml/blob/3.12.0/LICENSE),
checked 2026-09-25. The corresponding
[map](https://github.com/ocaml/ocaml/blob/3.12.0/stdlib/map.ml) and
[set](https://github.com/ocaml/ocaml/blob/3.12.0/stdlib/set.ml) headers carry
the same INRIA attribution and exception reference as Lem's copies.
Lem's initial Git import is `c99e3f59b5b7963c00f827e3634985dcdf23e43b`
(2013-03-06); this is source-notice restoration, not a new licensing grant
or a legal conclusion about a particular downstream distribution.
The separate `src/ulib` LGPL 2.1-or-later terms are unchanged.

The `opam` metadata lists the base licenses BSD-3-Clause, BSD-2-Clause,
LGPL-2.0-only and LGPL-2.1-or-later; per-file scope and exceptions remain in
LICENSE. Original runtime code follows Lem's BSD-3-Clause default. The
copied cap wrapper carries Cerberus's BSD-2-Clause notice. `make install`
ships LICENSE beside `lean-lib`, so its relative notice links survive an
opam installation.

Distributions of the runtime should carry the root LICENSE and these
source notices. Neither the Lean port nor its proof/test results erase the
upstream attribution or turn the entire runtime into BSD-only code.

Maintainer confirmation of the Lean-translation classification under the inherited exception remains open (public-readiness sweep, 2026-09-25 [AGENT]; the review's T3 note). No ruling is recorded here.
