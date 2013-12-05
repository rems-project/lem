% Lem Manual
% 
% 5th Dec. 2013

<link href="http://kevinburke.bitbucket.org/markdowncss/markdown.css" rel="stylesheet"></link>

# Introduction

Lem is a lightweight tool for writing, managing, and publishing large scale
semantic definitions. It is also intended as an intermediate language for
generating definitions from domain-specific tools, and for porting definitions
between interactive theorem proving systems (such as Coq, HOL4, and Isabelle).

It resembles a pure subset of Objective Caml, supporting typical functional
programming constructs, including top-level parametric polymorphism, datatypes,
records, higher-order functions, and pattern matching. It also supports common
logical mechanisms including list and set comprehensions, universal and
existential quantifiers, and inductively defined relations. From this, Lem
generates OCaml, HOL4 and Isabelle code.

# Installation

## Lem binary

To build Lem run `make` in the top-level directory. This builds the executable `lem`, and places a symbolic link to it in that directory. Lem depends on [OCaml](http://caml.inria.fr/). Lem is tested against OCaml 3.12.1. and 4.00.0. Other versions might or might not work.

Lem needs to access it's library, which is by default stored in `PATH_TO_LEM/library`. If you want to use a different library directory, please either set the environment variable `LEMLIB` or pass the command-line argument `-lib YOUR_LIB_DIR` to Lem when running it.

## Backend libraries

Running `make` only generates Lem itself. It does not generate the libraries needed to use Lem's output for certain backends. To generate the libraries for a specific backend, please run

    for OCaml   : make ocaml-libs
    for HOL 4   : make hol-libs
    for Isabelle: make isa-libs
    for Coq     : make coq-libs

These targets depend on the corresponding tool being installed, because they might run some automated tests or compile the Lem generated files. If you just want to generate the input, which Lem gives to these tools, please run `make libs`.

## Documentation

### Library documentation
Similar to generating backend libraries, one can also generate documentation for the libraries by running `make tex-libs`. This generates a file `tex-lib/lem-libs.pdf`. In order to not pretty print the whole library, but just get interface information, one can use Lem's command line argument `print_env`. Running `lem -print_env library/pervasives_extra.lem` loads all of the libraries and afterwards prints the environment in a concise form.

### Syntax
The input syntax of Lem is defined using the [Ott tool](http://www.cl.cam.ac.uk/~pes20/ott/). The language definition
can be found in file `language/lem.ott`. You don't need Ott to compile or use Lem. However, if Ott is installed, the makefile
in directory `language` can be used to generate a PDF documenting
the syntax of Lem.

### Papers
In subdirectory `doc`, a draft version of a PLDI submission 
describing Lem can be found.

### Old Manual
Lem's old manual can be found in subdirectory `manual`. It is
out of date, though. 

### New Manual
Lem's new manual can be found in subdirectory `doc` (as you know since you are reading it). It's written in *Markdown* and tested with
[Pandoc](http://johnmacfarlane.net/pandoc/) 1.9.1.1. However, it tries to avoid Pandoc specific extensions of Markdown.

Running `make` in subdirectory `doc` invokes Pandoc to generate html- and pdf-versions of the manual. Since the manual is written in Markdown, you can easily read it with the text-editor of your choice as well.

### Source code
The makefile in Lem's root directory contains targets to generate Ocamldoc documentation for Lem's sources. Running `make lem-doc` generates 

 - directory `html-doc` (the source documentation as HTML)
 - file `lem-doc.pdf` (the source documentation as PDF)
 - file `lem-doc-dep.pdf` (a dependency graph as PDF)


# Usage

TODO

