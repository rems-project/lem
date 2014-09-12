# Lem

Lem is a tool for lightweight executable mathematics, for writing,
managing, and publishing large-scale portable semantic definitions,
with export to LaTeX, executable code (currently OCaml) and
interactive theorem provers (currently Coq, HOL4, and Isabelle/HOL).

It is also intended as an intermediate language for generating
definitions from domain-specific tools, and for porting definitions
between interactive theorem proving systems.

Lem is under active development and has been used in several
applications, some of which can be found in the `examples` directory.
It is made available under the BSD 3-clause license, with the
exception of a few files derived from OCaml, which are under the
GNU Library GPL.

Lem depends on [OCaml](http://caml.inria.fr/). Lem is tested against OCaml
3.12.1. and 4.00.0. Other versions might or might not work.

To build Lem run 'make' in the top-level directory. This builds the
executable 'lem', and places a symbolic link to it in that directory.
Instructions on building the libraries for particular targets are in the
manual.

Documentation can be found in `doc/built-doc`, including:

* a high-level description of Lem in the draft paper `lem-draft.pdf`;
* the manual, in `lem-manual.html` and `lem-manual.pdf`;
* the Ott grammar and type system for Lem, in `lem.pdf`, built from the definition in language/lem.ott;
* the Lem library documentation, in `lem-libs.pdf`;
* the type signatures of the pervasives and pervasives-extra libaries, in `lem-libs-pervasives.txt` and `lem-libs-pervasives-extra.txt`; and
* source documentation, in `html-doc` and `lem-doc.pdf`, with a dependency diagram of the source modules in `dep.pdf`.

# Supported versions of software

Lem is tested against the following versions of the backend software:

  * OCaml: 3.12.1, 4.00.0, and 4.01.0
  * Coq: 8.4pl3 and 8.4pl2
  * Isabelle: Isabelle-2013-2
  * HOL: HOL4 Kananaskis 9