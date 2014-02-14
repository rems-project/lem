# Writing your own Lem files

Lem's syntax broadly follows OCaml syntax, while the libraries follow the Haskell libraries. Here, only a few selected points of Lem's syntax and its features are discussed. To learn more about its syntax, please have a look at the next section and at the file `doc/lem.pdf`. Another possibility is having a look at the Lem-library in the `library`-directory or at the tests in directory `tests`, especially `tests/backends`.

## Header

### Importing Library
A Lem file usually starts with importing the appropriate library. Without such an import, even very simple operations like boolean conjunction are not available. The user thus has the choice of either importing the main library or the extended library. The main library 
contains total, terminating functions that we believe are well-specified enough to be portable across all backends. All other functions are placed in the extended library. 

The main library is imported by

    open import Pervasives

and the extended one by

    open import Pervasives_extra
	
### Setting Module Name
Each Lem file defines a top-level module. A file with name `mymodule.lem` creates a Lem module `Mymodule`. By default this is also the name of the module for all backends. It is however possible (and sometimes necessary) to rename modules for backends. For example, 
Lem's library contains a file `set.lem`, which defines the Lem module `Set`. In order to avoid clashes with the existing HOL and Isabelle theories called set, it is however renamed to `lem_set` for these backends. This is done via the command

    declare {isabelle;hol} rename module = lem_set

Notice that in contrast to renaming functions, no module name is used
behind the keyword `module`. This causes the current module to be renamed. It is also possible to rename other modules. However, this should only be used for submodules defined in the same file as the renaming, because otherwise the module might have different names in different files referring to it.

### Importing Modules
Lem provides dependency resolution, but only for explicitly imported modules. Using a statement like

    import Mymodule
	
causes Lem to search for a file `mymodule.lem` in the current directory as well as in a list of given library directories. If such a file is found, it is automatically processed by Lem and it's contents are used to generate a Lem module `Mymodule`. Import statements do not need to, but are usually placed at the top of Lem files.


### Opening / Including Modules
A function `myfun` from a module `Mymod` is usually accessible by `Mymod.myfun`. Lem allows explicitly opening modules via `open Mymod`. After such a statement `myfun` can be used instead of `Mymod.myfun`.

When using `open Mymod` inside a module `Mymod2`, it only affects the state inside this current module `Mymod2`. It does not change the outside view of `Mymod2`. If you want to be all functions `Mymod.myfun` also available as `Mymod2.myfun`, one can use `include` instead of `open`. Including is mostly useful for writing libraries.

Often one wants to import and open a module at the same time. Therefore `open import Mymodule` and `include import Mymodule` are hands for first importing and then opening / including a module. Similarly, Lem allows opening/including/importing multiple modules with just one statement.

## Constant definitions

### Simple definitions
A simple function definition is Lem is very similar to an OCaml top-level definition. It is of the form

    let fun_name arg1 ... argn = rhs_exp 
	
The arguments are allowed to be arbitrary Lem-patterns. The right-hand side an arbitrary expression that uses the variables bound by the arguments. 

### Target specific definitions
Sometimes you might want to use different definitions for different targets. In order to do that the functions needs to be introduced via a val-specification first:

    val fun_name : type-scheme 

After this specification multiple target-specific definitions of the form

    let {target1; ...; targetn} fun_name arg1 ... argn  = rhs_exp

or
    let ~{target1; ...; targetn} fun_name arg1 ... argn  = rhs_exp 
	
are allowed. Thereby `{target1; ...; targetn}` represents the set of the given targets, whereas `~{target1; ...; targetn}` represents the set of all targets except the given ones. The targets intended to just typeset the Lem input file, i.e. the LaTeX and HTML do not require definitions and providing one does not change their behaviour. All other targets for which the function should be used, require a definition. 


### Inlining
Lem allows inlined constant definitions. These definitions are essentially macro expansions. For example consider an emptiness check for List.

    let inline isEmptyList l = (l = [])
	
It is a simple, straightforward definition, that you might not want to generate special target definitions for. An `inline` definition
allows using the function `isEmptyList` in Lem. It is also used in the HTML, Latex, Identity and Refactoring backends. All other backends replace it with the right hand side though. So, Lem would not define HOL4 function for `isEmptyList`, but replace every occurrence of it with the definition.

In order to allow this inlining, the definition has to be simple. Arguments are just allowed to be variables and inlined definition may not be recursive. Moreover, they may not have any type-class constraints attached. 

If a val-specification is provided first, it is possible to inline constants only for certain targets and generate proper definitions for other targets. For this, syntax similar to the following example is used:

    let inline {hol} isEmptyList l = (l = [])

### Recursive Definitions
Lem allows to define recursive and even mutually recursive functions by using the keyword `let rec`. For example to define (stupidly) functions `even` and `odd`, one can use

    let rec even (0:nat) = true
	    and odd  0 = false
		and even (n + 1) = not (odd n)
		and odd (n + 1) = not (even n)

### Termination Proofs
Recursive definitions require termination (or well-foundedness) proofs in the theorem prover backends. Isabelle and HOL4 are able to delay these proofs. The user has to fill in these proofs then, before using the defined functions. For simple functions like the ones in the example, this can be annoying. A `termination_argument` declaration can therefore be used to tell Isabelle and HOL to try automatic termination proofs. If multiple functions are defined in a single, mutually recursive definition, an automatic termination proof is only attempted, if automatic termination is declared for all defined functions.

    declare {hol; isabelle} termination_argument even = automatic
    declare {hol; isabelle} termination_argument odd = automatic


## Type definitions

Note that when defining new types in Lem it may be necessary to
instantiate some of the basic type classes, as described in the Type
Classes section below.


## Assertions / Lemmata / Theorems
Lem allows the user to write assertions, lemmata and theorems. These are named boolean expressions, which the user desires to be true. For the append function on lists, one could for example write:

    assert append_test_1: [(2:nat); 3] ++ [4;5] = [2;3;4;5]
    lemma append_spec: (forall l. [] ++ l = l) && (forall x xs ys. (x :: xs) ++ ys = x :: (xs ++ ys))
    theorem append_empty: forall l. l ++ [] = l

*Assertions* should be executable. They are intended to be used for unit-testing your Lem specifications. For OCaml and HOL4 they generate executable tests. 

*Lemmata* are non-executable properties. They are used to document properties that are non-executable. They can be used for documentation purposes to write down properties the user had in mind, when defining a function. They generate proof obligation in the auxiliary files. Therefore, they can also be used to express important high-level properties about the whole model, which the user wants to proof correct.  *Theorems* are lemmata that the user wants to mark as important.

Writing assertions allows an easy way to unit-test specifications. Lemmata and theorems are beneficial for documentation purposes. The automated translation to Isabelle also allows to use Isabelle's sophisticated automation without knowing much about Isabelle. With that mechanism it is for example very easily possible to search for counter-examples.


## Renaming
The naming conventions of our backends differ. Therefore, it might be beneficial to use different names depending on the backend. Renaming can also be used to avoid name clashes with existing backend functions or just to avoid confusion when similar names already are used for the backend. For example, there is already a HOL4 function `symmetric`. To avoid confusion with the Lem function `isSymmetric` the Lem one can easily be renamed:

    declare {hol} rename function isSymmetric = lem_is_symmetric



Besides `function`s, it is also possible to rename `type`s, `field`s and `module`s. 


