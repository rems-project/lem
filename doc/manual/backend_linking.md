# Linking to existing Backend Libraries

Lem allows one to use existing backend libraries from your Lem-development. This is done by target-specific imports and target-specific representations.

## Target specific imports
Before using an existing target library, it usually needs to be loaded. There are target-specific `open`, `import` and `include` statements that allow instructing Lem to generate output that loads an existing backend library. These statements are very similar to the corresponding statements for Lem modules. However, they allow specifying targets and the modules are quoted. While - generalising the Lem staments - many possible combinations are allowed, in practice only `open import` statements are used. 

As an example, consider Lem's relation library. Some of its existing definitions should be mapped to HOL functions defined in the HOL4 theory `set_relation`. To load this theory for HOL, Lem's relation library contains the statement

    open import {hol} `set_relationTheory`
	

## Simple Target Representations
A `target_rep` declaration allows specifing which _existing_ target function should be used for a Lem-specific one. The boolean conjunction operator is for example mapped as follows
    
    val not : bool -> bool
    let not b = match b with
      | true -> false
      | false -> true
    end
    
    declare ocaml    target_rep function not = `not`
    declare hol      target_rep function not x = `~` x
    declare isabelle target_rep function not x = `\<not>` x
    declare coq      target_rep function not = `negb`

    declare html     target_rep function not = `&not;`
    declare tex      target_rep function not b = `$\neg$` b

- definition + target rep useful for documentation
- however, only val-spec + target rep needed
- definition gets turned into lemma when target-rep is present
- rhs of target_reps can be expression containing quotations
- if arguments are given, they have to be variables
- if not all arguments are present, eta-expansion is used
- eta-expansion necessary sometimes, see `not` for Isabelle and HOL


## Target Representations of Types

    type map 'k 'v
    declare ocaml    target_rep type map = `Pmap.map` 
    declare isabelle target_rep type map = `Map.map` 
    declare hol      target_rep type map = `fmap`
    declare coq      target_rep type map = `fmap`


## Infix Operations

    val (&&) [`and`] : bool -> bool -> bool
    let (&&) b1 b2 = match (b1, b2) with
      | (true, true) -> true
      | _ -> false
    end
    
    declare hol      target_rep function (&&) = infix `/\`
    declare ocaml    target_rep function (&&) = infix `&&`
    declare isabelle target_rep function (&&) = infix `\<and>`
    declare coq      target_rep function (&&) = infix `&&`
    declare html     target_rep function (&&) = infix `&and;`
    declare tex      target_rep function (&&) = infix `$\wedge$`


## Special Target Representations

    class ( NumPow 'a ) 
      val ( ** ) [`numPow`] : 'a -> nat -> 'a
    end
    declare tex target_rep function numPow n m = special "{%e}^{%e}" n m
