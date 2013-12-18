# Lem-library
Lem comes with a default library of types and constants. This library can be found in directory `library`.
It contains collections such as lists, sets and maps, basic data types such as disjoint sums, optional types, booleans and tuples, useful combinators on functions, and a library for working with relations.

## General Design
The library follows Haskell's library in terms of names of constants, types and modules. The library is separated into two sets of modules: the *main* and *extra* modules. The main hierarchy of files contain total, terminating functions that we believe are well-specified enough to be portable across all backends. All other functions are are placed in the extra modules. For example, the library file `function.lem` includes various useful combinators such as `flip` and `const`. The `function_extra.lem` file, on the other hand, contains the constant `THE` with type `forall 'a. ('a --> bool) --> maybe 'a`, inexpressible in Coq.

Lem leaves the choice of using the main library or the extended library to the user. The module `Pervasives` contains the main part of the library, `Pervasives_extra` the extra part. The first line of a common Lem file is usually `open import Pervasives` or `open import Pervasives_extra`, which imports and opens either the main or the extra library.


## Library documentation
For an overview of the Lem library, please generate the pdf-file
`tex-lib/lem-libs.pdf` by running `make tex-libs`. If you are just interested in the interface, consider running `lem -print_env library/pervasives_extra.lem`.

