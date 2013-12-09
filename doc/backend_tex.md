## LaTeX

The command line option `-tex` instructs Lem to generate LaTeX output. A module with name `Mymodule` generates a files `Mymodule.tex`,
`Mymodule-inc.tex` and `Mymodule-use_inc.tex`. No auxiliary files are generated. The generated LaTeX output depends on the style-file `lem.sty` in directory `tex-lib`.

The file `Mymodule.tex` contains a pretty-printed version of the original input file. `Mymodule-inc.tex` defines LaTeX macros that can be used to type-set single definitions inside your own developments. `Mymodule-use_inc.tex` uses these macros to mimic the behaviour of `Mymodule.tex`. It is useful, since it essentially is a list of all the defined macros in the order they appear in the input file.

The command-line-option `-tex` generates separate LaTeX files for each input file. If using the option `-tex_all my_output`, Lem generates the files `my_output.tex`, `my_output-inc.tex` and `my_output-use_inc.tex`, which contain representations / macros for all input files.


### LaTeX Macro Names
The `...-inc.tex` files contain macros that allow type-setting single definitions from the original input. As far as possible, the names of the macros are derived from the name of the defined entity. We have

- the definition of a function `myfun` generates a macro `\LEMmyfun`
- the definition of a type `mytype` generates a macro `\LEMTypeMytype`
- the definition of a relation `myrel` generates a macro `\LEMmyrel`
- a val-specification of a function `myfun` generates a macro `\LEMValspecMyfun`

Other entities like declarations, class definitions etc. do not currently get predictable names. Please have a look at the content of the `...-use_inc.tex` or `...-inc.tex` file to figure out the generated name for these.

If the names of macros derived by the scheme above clash, a number is added at the end. Because LaTeX does not allow digets in macro names, these numbers are expressed as English words. Name clashes happen if there are several definitions of a function, which sometimes happens since you might prefer a different definition depending on the target. If there is a val-specification for a function `myfun`, as well as an OCaml-specific, a HOL and Isabelle-specific and Coq-specific one, these generates the macros `\LEMValspecMyfun`, `\LEMmyfun`, `\LEMmyfunZero`, `\LEMmyfunOne`, `\LEMmyfunTwo`. 


### LaTeX Macro Usage
By default, macros print their full definition without any preceding comment, but with a LaTeX `label` that allows referring to that definition. The generated LaTeX macros accept an optional argument that changes this behaviour. So, for example `\LEMmyfun` prints the definition of the function `myfun`, whereas `\LEMmyfun[name]` prints only the type-set name of `myfun`. 
There are the following arguments available:

- `default` same as not providing an argument, alias for `def`
- `def` print a label followed by the full definition excluding the preceding comment
- `defWithComment` print a label followed by the full definition including the preceding comment 
- `name` print the typeset name of the definition. For definitions defining more than one constant of type, as well as for Lem statements not defining anything, this is empty
- `comment` print the preceding comment
- `commentPre` alias for `comment`
- `commentPost` print the comment directly after the definition (usually empty)
- `core` print the *core* of a definition. Usually that's the right hand side of the definition, but might vary depending on the type of Lem-statement that generated the macro
- `label` print the label that is used by `def` and `defWithComment`.

If you want to learn about details or add your own argument values, please have a look at the definition of macro `\lemdefn` in file `tex-lib/lem.sty`.

### Libraries
Running `make tex-libs` in Lem's main directory generates LaTeX output for Lem's library. By running Pdflatex on this output a file `tex-lib/lem-libs.pdf` is generated, which can be used as library documentation. Moreover, there are also `lem-libs.tex`, `lem-libs-inc.tex` and `lem-libs-use_inc.tex`, which can be used as described above.

