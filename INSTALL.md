# Lem install

## Lem binary

To build Lem run "make" in the top-level directory. This builds the
executable lem, and places a symbolic link to it in that directory. Now
set the `LEMLIB` environment variable to `PATH_TO_LEM/library`, or
alternately pass the `-lib PATH_TO_LEM/library` flag to lem when you
run it. Lem depends on [OCaml](http://caml.inria.fr/). Lem is tested against OCaml
3.12.1. and 4.00.0. Other versions might or might not work.

## Backend libraries

Running "make" only generates Lem. It not generate the libraries needed to use 
Lem's output for certain backends. To generate the libraries for a specific backend, 
please run

for OCaml   : make ocaml-libs
for HOL 4   : make hol-libs
for Isabelle: make isa-libs
for Coq     : make coq-libs

These targets depend on the corresponding tool being installed. If you just want to
generate the input, Lem gives to these tools, please run "make libs"

