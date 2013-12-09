#OTTLIB=/Users/sowens/ott/hol
OTTLIB=$(dir $(shell which ott))../hol

all: lem.pdf

lem.pdf: lem.tex
	pdflatex lem.tex

lemTheory.uo: lemScript.sml
	Holmake --qof -I $(OTTLIB) lemTheory.uo

lem.tex ../src/ast.ml lemScript.sml: lem.ott
	rm -f ../src/ast.ml
	ott  -ocaml_include_terminals true -o lem.tex -o ../src/ast.ml -o lemScript.sml -picky_multiple_parses true lem.ott
	chmod a-w ../src/ast.ml

# for ascii grammar
foo:
	ott  -alltt out.tex -showraw true -picky_multiple_parses true lem.ott


lem-inc.tex: lem.hacked.ott Makefile
	ott  -ocaml_include_terminals true -o lem-inc.pre.tex -tex_wrap false -picky_multiple_parses true lem.hacked.ott
	sed 's/\\_aux//g' lem-inc.pre.tex > lem-inc.tex

lem.hacked.ott: lem.ott Makefile
	grep -v NOPLDI lem.ott | sed 's/%PLDIlHACK/{{ tex }}/g' | sed 's/\^{l}//g' > lem.hacked.ott

lem.lem: lem.ott
	ott -o lem.lem -picky_multiple_parses true lem.ott


clean:
	rm -rf *~
	-rm -rf *.uo *.ui lemTheory.sig lemTheory.sml lem.tex lemScript.sml lem.aux lem.log lem.dvi lem.ps lem_unwrapped.tex .HOLMK lem-inc.tex lem.hacked.ott
#lem.sys lem library/lib_cache

