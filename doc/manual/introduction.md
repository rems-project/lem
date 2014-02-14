# Introduction

Lem is a lightweight tool for writing, managing, and publishing large scale
semantic definitions. It is also intended as an intermediate language for
generating definitions from domain-specific tools, and for porting definitions
between interactive theorem proving systems (such as Coq, HOL4, and Isabelle).

The language combines features familiar from functional programming languages with logical constructs. 
From functional programming languages we take
pure higher-order functions,
general recursion,
recursive algebraic datatypes, 
records,
lists,
pattern matching,
parametric polymorphism,
a simple type class mechanism for overloading, and
a simple module system.
To these we add logical constructs familar in provers:
universal and existential quantification,
sets (including set comprehensions), relations,  finite maps, 
inductive relation definitions, and
lemma statements.
Then there are facilities to let the user tune how Lem definitions are
mapped into the various targets (by declaring target representations
and controlling notation, renaming, inlining, and type classes), to generate
witness types and executable functions from
inductive relations, and for assertions.


Lem typechecks its input and can 
generate executable OCaml, 
theorem prover definitions in Coq, HOL4 and Isabelle/HOL, 
typeset definitions in LaTeX, and simple HTML.

## Supported software

Lem is tested against the following versions of the backend software:

  * OCaml: 3.12.1. and 4.00.0
  * Coq: 8.4pl3 and 8.4pl2
  * Isabelle: Isabelle-2013-2
  * HOL: HOL4 Kananaskis 9

Older or newer versions of this software may work correctly with Lem, but are unsupported.


