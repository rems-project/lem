Lem Sources

This file contains some top-level description of the files 
shipped with Lem. A detailed documentation of the OCaml code is
available via the ocamldoc documentation, which can be generated via
"make lem-doc".

top-level directory structure:

etc/          headers and similar things
language/     the definition of the source language 
                The Lem implementation uses the OCaml AST generated from 
                this Ott description. Moreover, the generated Lem.pdf is
                useful to understand the input syntax.
library/      the Lem standard library - all .lem code, including Lem
                descriptions of stuff available in the backends, but no
                backend code (that's in ocaml-lib/, tex-lib/ ...)
Makefile      including targets for packaging a distro etc.
manual/       the Lem user reference manual (pretty sketchy)
ocaml-lib/    OCaml implementations of bits of the Lem standard library
coq-lib/      Coq implementations of bits of the Lem standard library
isabelle-lib/ OCaml implementations of bits of the Lem standard library
hol-lib/      HOL 4 implementations of bits of the Lem standard library
tex-lib/      lem.sty
tests/        the test suites and plumbing for them
src/          the Lem sources, i.e. .ml and .mli files


The processing of a bunch of .lem files goes like this:

0) top-level driver, in main.ml and process_file.ml

1) initial_env.ml, pulls in the library subdirectory and constructs an
    initial environment 

2) lexing and parsing of the .lem source, by lexer.mll and parser.mly,
    which gives an untyped-AST value (a value of type Ast.defs, where
    ast.ml is the Ott-generated AST).

3) typechecking, by typecheck.ml (the main file) and types.ml (a major
    helper), which gives a typed-AST value (a value of type
    Typed_ast.defs, where typed_ast.ml is hand-written).

4) running the backends. The target_trans.ml file is the driver of the
    typed-ast-to-typed-ast translation process. What it does in particular
    can be configured for each backend. However, there are roughly the following
    steps, which are applied till nothing more can be done:
     

    - Something is done at the definition level (eg in HOL it
    translates away value definitions; in OCaml it erases any inductive
    relation definitions). These macros live in def_trans.ml and the
    macro expander is in def_trans.ml.
 
    - Macro expansion happens on expressions (eg in HOL
    it translates away list comprehensions; in OCaml it translates
    away all comprehensions). It also inlines let-inline definitions.
    All these macros live in trans.ml and the macro-expander code lives
    in macro_expander.ml.

    - It does some extra processing that doesn't fit into the
    macro-expansion setup, eg renaming to mess with the name
    capitalisation.  (The macro expander tries to check that the
    result of applying macros are typed; this doesn't).

    (there's some model of how the backends understand lexing and
    parsing, to add enough parens and deal with infix etc., but at
    present we *don't* have a good model of the backend-specific
    lexical structure, eg identifier capitalisation and binding
    structure).

5) Generate actual backend code, in backend.ml, using output.ml (which
   puts in spaces whenever the target would have lexed things too
   glommed up)

