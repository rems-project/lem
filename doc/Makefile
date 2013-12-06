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

all: lem-manual.html lem-manual.pdf

clean:
	rm -f lem-manual.md 

lem-manual.md : $(INPUT_FILES)
	cat $(INPUT_FILES) > lem-manual.md

lem-manual.html : lem-manual.md
	pandoc -s --number-sections --toc lem-manual.md -o lem-manual.html

lem-manual.pdf : lem-manual.md
	pandoc -s --number-sections --toc lem-manual.md -o lem-manual.pdf

