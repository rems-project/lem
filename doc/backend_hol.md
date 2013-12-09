## HOL4

The command line option `-hol` instructs Lem to generate HOL4 output. A module with name `Mymodule` generates a file `mymoduleScript.sml` and possibly `mymoduleAuxiliaryScript.sml`. 

### Compilation
Lem-generated HOL theories depend on some Lem-specific HOL4 code as well as HOL4 versions of the Lem library. Calling `make hol-libs` in Lem's main directory generates these files in subdirectory `hol_lib` and compiles them using `Holmake`. During this compilation process a heap with name `lemheap` is generated. It is recommended to use this heap for your own HOL4 development based on Lem-generated files. Using the generated files in `hol-libs` directly is possible as well, though. In order to use the heap, add the following line to the `Holmakefile` of the directory, where your HOL4-files are stored:

    HOLHEAP = path_to_lem/hol-lib/lemheap

A template `Holmakefile` file using other useful options as well can be found in directory `library`. 

### Auxiliary Files
HOL4 auxiliary files contain both executable tests generated from assertions as well as templates for termination proofs and lemmata that need manual labour by the user. The command line option `-auxiliary_level auto` allows to generate only the executable tests.


