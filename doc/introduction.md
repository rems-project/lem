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

