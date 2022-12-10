# Lem

Lem is a tool for lightweight executable mathematics, for writing,
managing, and publishing large-scale portable semantic definitions,
with export to LaTeX, executable code (currently OCaml) and
interactive theorem provers (currently Coq, HOL4, and Isabelle/HOL,
though the generated Coq is not necessarily idiomatic).  It is also
intended as an intermediate language for generating definitions from
domain-specific tools, and for porting definitions between interactive
theorem proving systems.

The language, originally based on a pure fragment of OCaml, combines
features familiar from functional programming languages with logical
constructs. From functional programming languages we take pure
higher-order functions, general recursion, recursive algebraic
datatypes, records, lists, pattern matching, parametric polymorphism,
a simple type class mechanism for overloading, and a simple module
system. To these we add logical constructs familiar in provers:
universal and existential quantification, sets (including set
comprehensions), relations, finite maps, inductive relation
definitions, and lemma statements. Then there are facilities to let
the user tune how Lem definitions are mapped into the various targets
(by declaring target representations and controlling notation,
renaming, inlining, and type classes), to generate witness types and
executable functions from inductive relations, and for assertions.

Lem has been used in several applications, some of which can be found
in the `examples` directory.  As of 2020, Lem remains in continuous
use but is not under active development.



## Papers

* [Lem: Reusable Engineering of Real-world Semantics](http://www.cl.cam.ac.uk/~pes20/lem/built-doc/lem-icfp-2014.pdf). Dominic P. Mulligan, Scott Owens, Kathryn E. Gray, Tom Ridge, and Peter Sewell. In ICFP 2014.
    
* [Lem: A Lightweight Tool for Heavyweight Semantics](https://doi.org/10.1007/978-3-642-22863-6_27). Scott Owens, Peter Böhm, Francesco Zappa Nardelli, and Peter Sewell. In ITP 2011 (Rough Diamond).

## Documentation

Documentation can be found in `doc/built-doc`, including:

* the [manual](https://www.cl.cam.ac.uk/~pes20/lem/built-doc/lem-manual.html), in `lem-manual.html` and `lem-manual.pdf`;
* the [Ott grammar and type system for Lem](https://www.cl.cam.ac.uk/~pes20/lem/built-doc/lem.pdf), in `lem.pdf`, built from the definition in `language/lem.ott`;
* the [Lem library documentation](https://www.cl.cam.ac.uk/~pes20/lem/built-doc/lem-libs.pdf), in `lem-libs.pdf`;
* the type signatures of the [pervasives](https://www.cl.cam.ac.uk/~pes20/lem/built-doc/lem-libs-pervasives.txt) and [pervasives-extra](https://www.cl.cam.ac.uk/~pes20/lem/built-doc/lem-libs-pervasives.txt) libaries, in `lem-libs-pervasives.txt` and `lem-libs-pervasives-extra.txt`; and
* source documentation, in [`html-doc`](https://www.cl.cam.ac.uk/~pes20/lem/built-doc/html-doc) and [`lem-doc.pdf`](https://www.cl.cam.ac.uk/~pes20/lem/built-doc/lem-doc.pdf), with a dependency diagram of the source modules in [`dep.pdf`](https://www.cl.cam.ac.uk/~pes20/lem/built-doc/dep.pdf).


## To install and build

Lem is available as 
an [opam](https://opam.ocaml.org) package and a 
[github repo](https://github.com/rems-project/lem).

### With OPAM  (released version)

First, ensure you have opam (the OCaml package manager) installed,
version 2.0 or greater (opam 1 versions of Lem are no longer
supported).  You can use your system's package manager e.g. `sudo
apt-get install opam` (e.g. on Ubuntu 20.04) or follow the
[instructions from the opam website](https://opam.ocaml.org/doc/Install.html).
On older Ubuntu versions you will not be able to use their package
manager's opam 1 version, and will need to install opam 2 following the
instructions on the opam website.

Then `opam install lem` will install the latest Lem version.  


### With OPAM (github checkout)

In the checkout directory, run `opam pin add lem .`.

To rebuild and reinstall after local changes, run `opam upgrade --working-dir lem`  (or `opam upgrade -w lem`).

### Without OPAM

The command `make` (`make world`) builds the `lem` binary, and places a symbolic link to it in the top-level directory.
Now set the `LEMLIB` environment variable to `PATH_TO_LEM/library`, or alternately pass the `-lib PATH_TO_LEM/library` flag to `lem` when you run it.

## Backend libraries

Running `make` only generates Lem. It not generate the libraries needed to use Lem's output for certain backends. To generate the libraries for a specific backend, please run

- for OCaml : `make ocaml-libs`
- for HOL4 : `make hol-libs`
- for Isabelle: `make isa-libs`
- for Coq : `make coq-libs`

These targets depend on the corresponding tool being installed. If you
just want to generate the input that Lem gives to these tools, please
run `make libs`.

## Dependencies

Lem depends on [OCaml](http://caml.inria.fr/). Lem has been tested
against OCaml `4.07.0`, `4.12.0` and `5.0.0~beta1`. Other versions might or
might not work.  Lem requires the OCaml ZArith library for arbitrary
precision arithmetic.  Lem has been tested against ZArith version
`1.4` and `1.9.1`.  Other versions might or might not work.

The generated Isabelle theories require the `Word_Lib` entry of the [Archive of
Formal Proofs](https://www.isa-afp.org/) to be installed and set up (e.g. by
adding the path to `Word_Lib` to `$ISABELLE_HOME_USER/ROOTS`).  An Isabelle
2022 version of the AFP can be downloaded
[here](https://foss.heptapod.net/isa-afp/afp-2022).

## Supported versions of target software

Lem has been tested against the following versions of the backend software:

  * OCaml: `4.07.0`, `4.12.0` and `5.0.0~beta1`
  * Coq: 8.16.0
  * Isabelle 2022
  * HOL: HOL4 Kananaskis 14

## Examples

The `examples` directory in the repository contains or points to several of the early major examples of Lem usage:

* The operational model for Power/ARM multiprocessor concurrency by Sarkar et al., as described in PLDI11 and extended in POPL12, PLDI12 (ppcmem-model)
* The C/C++11 axiomatic concurrency model by Batty et al., as described in POPL11 and extended in the above two POPL12 and PLDI12 papers (cpp)
* The OCaml_light semantics by Owens, as described in ESOP2008 (ocaml_light)
* The NetSem models for the TCP/IP network protocols and Sockets API by Bishop et al., as described in TACS01, ESOP02, SIGCOMM 2005, POPL 2006, FM08, are available from the github repository <https://github.com/PeterSewell/netsem>, ported into Lem from the original HOL4.
* The CakeML development by Kumar et al., described in ICFP12, ITP13, and POPL14, is available via its web page: <https://cakeml.org.>


## Lem and Ott

Lem shares many of the goals of our Ott tool: both emphasize source
readability, and multi-prover compatibility. However, Lem is a
general-purpose specification language, whereas Ott is a
domain-specific language for writing specifications of programming
languages (i.e., inductive relations over syntax). Thus, Ott supports
rich user-defined syntaxes, whereas Lem supports functional
programming idioms. The two can be used together in some cases: Ott
can now generate Lem specifications.



## History

- 2018-01-31: moved to github
- 2013-12-13: updated with links to current documentation and examples
- 2013-03-14: Moved page to Kent, removed 0.3 release, and updated for open source development on Bitbucket
- 2011-12-02: Lem 0.3 posted (minor changes from 0.2)
- 2011-08-22: Lem 0.2 posted, manual added
- 2011-05-25: ITP 2011 paper added
- 2011-04-11: Lem 0.1 posted
- 2011-03-24: Web page created

## People

Lem has been developed principally by 
Dominic Mulligan,
Kathryn E. Gray,
Scott Owens,
Peter Sewell, and
Thomas Tuerk;
 with additional contributions from
Basile Clement,
Brian Campbell,
Christopher Pulte,
David Sheets,
Fabian Immler
Frederic Loulergue,
Francesco Zappa Nardelli.
Gabriel Kerneis,
James Lingard,
Jean Pichon-Pharabod,
Justus Matthiesen,
Kayvan Memarian,
Kyndylan Nienhuis,
Lars Hupel,
Mark Batty,
Michael Greenberg
Michael Norrish,
Ohad Kammar,
Peter Boehm,
Robert Norton
Sami Mäkelä,
Shaked Flur
Stephen Kell,
Thibaut Pérami,
Thomas Bauereiss,
Thomas Williams,
Victor Gomes, and
emersion.



## License

Lem is made available under the BSD 3-clause license, with the
exception of a few files derived from OCaml, which are under the
GNU Library GPL.
