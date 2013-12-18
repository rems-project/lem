## OCaml

The command line option `-ocaml` instructs Lem to generate OCaml output. A module with name `Mymodule` generates a file `mymodule.ml` and possibly `mymoduleAuxiliary.lem`. 

### Compilation
Lem-generated OCaml relies on some Lem-specific OCaml code as well as OCaml versions of the Lem library. Calling `make ocaml-libs` in Lem's main directory generates these files in subdirectory `ocaml_lib` and
compiles them. 

When compiling Lem-generated OCaml-code, it needs to be linked with the files in directory `ocaml_lib`. To make this simpler, an OCaml-package `Lem` (using `extract.cma`) is defined in this directory. One can for example compile a file `name1.ml`
by

    ocamlc -I path_to_lem/ocaml-lib/_build -o name extract.cma name1.ml

or, using *ocamlbuild* and *findlib*, by

    export OCAMLPATH=/absolute/path/to/lem/ocaml-lib:$OCAMLPATH
    ocamlbuild -libs nums -use-ocamlfind -pkg lem name.native
	
### Auxiliary Files
OCaml auxiliary files do not need modifications by the user.
They contain tests generated from *assertions* in the input files.
When compiled as described above and run as standalone programs, 
OCaml auxiliary files execute the tests and print the results.

