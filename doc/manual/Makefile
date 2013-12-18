INPUT_FILES := \
  header.md \
  introduction.md \
  installation.md \
  invokation.md \
  backends.md \
    backend_ocaml.md \
    backend_hol.md \
    backend_isa.md \
    backend_coq.md \
    backend_tex.md \
    backend_html.md \
  library.md \
  own_lem_files.md \
  language.md \
  backend_linking.md \
  typeclasses.md \
  refactoring.md \


all: lem-manual.html lem-manual.pdf

clean:
	rm -f lem-manual.md lem-manual.html  lem-manual.pdf

lem-manual.md : $(INPUT_FILES)
	cat $(INPUT_FILES) > lem-manual.md

lem-manual.html : lem-manual.md
	pandoc -s --number-sections --toc lem-manual.md -o lem-manual.html

lem-manual.pdf : lem-manual.md
	pandoc  --template my-pandoc-latex-template.latex -s --number-sections --toc lem-manual.md -o lem-manual.pdf



#lem-language.pdf: 
#	make -C ../language && cp ../language/lem-language.pdf .
