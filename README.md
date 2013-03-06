# Lem

Lem is a tool for lightweight executable mathematics, for writing,
managing, and publishing large-scale semantic definitions, with export
to LaTeX, executable code (currently OCaml) and interactive theorem
provers (currently Coq, HOL4, and Isabelle/HOL).

It is also intended as an intermediate language for generating
definitions from domain-specific tools, and for porting definitions
between interactive theorem proving systems

This is a preliminary release of Lem which is not yet feature
complete.  It is released under the BSD 3-clause license, with the
exception of a few files derived from the OCaml, which are released
under the GNU Library GPL.

Lem depends on OCaml (http://caml.inria.fr/). Lem is tested against OCaml
3.12.1. Other versions might or might not work.

To build Lem run make in the top-level directory. This builds the
executable lem, and places a symbolic link to it that directory. Now
set the `LEMLIB` environment variable to `PATH_TO_LEM/library`, or
alternately pass the `-lib PATH_TO_LEM/library` flag to lem when you
run it. This tells Lem where to find its library of types for
HOL/Isabelle/OCaml/Coq built-in functions.

Please see the manual at http://www.cl.cam.ac.uk/~so294/lem/lem-manual.pdf or
http://www.cl.cam.ac.uk/~so294/lem/lem-manual.html.
