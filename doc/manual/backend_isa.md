## Isabelle/HOL

The command line option `-isa` instructs Lem to generate Isabelle/HOL output. A module with name `Mymodule` generates a files `Mymodule.thy` and possibly `MymoduleAuxiliary.thy`. 

### Generating Isabelle Library
Lem-generated Isabelle theories depend on some Lem-specific Isabelle theories as well as Isabelle versions of the Lem library. Calling `make isa-libs` in Lem's main directory generates these files in subdirectory `isa_lib`. In contrast to the HOL and OCaml libraries 
the generation of these libraries does not trigger automatic tests. If you want to check the sanity of the library, please use 
`make isa-lib-tests` in subdirectory library. This creates a directory
`library/isa-build-dir` and the library auxiliary files within this directory. Moreover, there is a file `LemTests.thy`, which imports all other files and is therefore useful for testing all these files in Isabelle. 


### Adapting Isabelle Imports
The theory import-statement in the header of generated Isabelle files contains the absolute path to Lem's library directory. If you move the library directory, this path needs adapting. If you want to use a backend specific `import` statement in your own Lem development, that imports some theory in the library directory, you can use the variable `$LIB_DIR` as in the following example

    open import {isabelle} `$LIB_DIR/Lem`


### Auxiliary Files 
Isabelle auxiliary contain both executable tests generated from assertions as well as templates for termination proofs and lemmata that need manual labour by the user. In contrast to the auxiliary output of HOL, the templates for lemmata and termination proofs make use of Isabelle's automation and therefore often succeed without user intervention. Therefore, using the command line option `-auxiliary_level auto` in order to generate only code for assertions is possible but not imperative. 


### Automatic Proof Tools / Counter Example Generation
The auxiliary files contain templates for lemmata that use Isabelle's automation. Therefore these templates might be useful even for users not familiar with Isabelle, who want to use tools like automatic counter example generation.

The Lem-lemma 

    lemma unzip_zip:
       forall l1 l2. unzip (zip l1 l2) = (l1, l2)

is for example translated to the following Isabelle code:

    lemma unzip_zip:
       "! l1 l2. list_unzip (zip l1 l2) = (l1, l2)"
       (* try *) by auto
	   
The automated proof attempt by the `auto` method fails. If the user removes the comment around `try`, various automated methods are run to either prove the lemma or find a counterexample. These methods include
running external SMT and first order provers, internal natural deduction tools as well as a sophisticated counter example generator.
In this example, Isabelle quickly finds a counterexample:

    Nitpick found a counterexample for card 'a = 2 and card 'b = 2:
      Skolem constants: l1 = [a1], l2 = []

While this is a trivial example, counterexamples and proofs are also found for more interesting cases. So, writing lemmata in Lem and translating them to Isabelle might be useful, even if you are not familiar with Isabelle. 

