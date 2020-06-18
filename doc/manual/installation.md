# Installation

## Lem binary

See the github README.

## Backend libraries

See the github README.

## Documentation 

See the github README for papers and the Lem manual

The manual and its sources can be found in subdirectory `doc`. It's written in *Markdown* and tested with
[Pandoc](http://johnmacfarlane.net/pandoc/) 1.9.1.1. However, it tries to avoid Pandoc specific extensions of Markdown.

Running `make` in subdirectory `doc` invokes Pandoc to generate html- and pdf-versions of the manual. Since the manual is written in Markdown, you can easily read it with the text-editor of your choice as well.

### Library documentation
Similar to generating backend libraries, one can also generate documentation for the libraries by running `make tex-libs`. This generates a file `tex-lib/lem-libs.pdf`. In order to not pretty print the whole library, but just get interface information, one can use Lem's command line argument `print_env`. Running `lem -print_env library/pervasives_extra.lem` loads all of the libraries and afterwards prints the environment in a concise form.

### Syntax
The input syntax of Lem is described later in this document. 
The syntax is defined using the [Ott tool](http://www.cl.cam.ac.uk/~pes20/ott/), and the language definition
can be found in file `language/lem.ott`. You don't need Ott to compile or use Lem. However, if Ott is installed, the makefile
in directory `language` can be used to generate a PDF documenting
the syntax of Lem.   A snapshot of that is in `doc/lem.pdf`.

### Source code documentation
The makefile in Lem's root directory contains targets to generate Ocamldoc documentation for Lem's sources. Running `make lem-doc` generates 

 - directory `html-doc` (the source documentation as HTML)
 - file `lem-doc.pdf` (the source documentation as PDF)
 - file `lem-doc-dep.pdf` (a dependency graph as PDF)


### Old Manual
Lem's old manual can be found in subdirectory `manual`. It is
now out of date, though. 


