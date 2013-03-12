#OTTLIB=/Users/sowens/ott/hol
OTTLIB=$(dir $(shell which ott))../hol

all: lem.pdf

lem.pdf: lem.tex
	pdflatex lem.tex

lemTheory.uo: lemScript.sml
	Holmake --qof -I $(OTTLIB) lemTheory.uo

lem.tex ../src/ast.ml lemScript.sml: lem.ott
	rm -f ../src/ast.ml
	ott -ocaml_include_terminals true -o lem.tex -o ../src/ast.ml -o lemScript.sml -picky_multiple_parses true lem.ott
	chmod a-w ../src/ast.ml


clean:
	rm -rf *~
	-rm -rf *.uo *.ui lemTheory.sig lemTheory.sml lem.tex lemScript.sml lem.aux lem.log lem.pdf lem.dvi lem.ps lem_unwrapped.tex .HOLMK 
#lem.sys lem library/lib_cache

