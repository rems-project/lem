all: lem-manual.pdf lem-manual.html

lem-manual.pdf: lem-manual.ps
	ps2pdf lem-manual.ps

lem-manual.ps: lem-manual.dvi
	dvips lem-manual.dvi

lem-manual.dvi: lem-manual.tex
	latex lem-manual.tex
	latex lem-manual.tex

lem-manual.tex: lem-manual.mng lem.tex
	rm -f lem-manual.tex
	ott -tex_filter lem-manual.mng lem-manual.tex ../language/lem.ott
	chmod a-w lem-manual.tex

lem-manual.html: hevea/bin/hevea lem-manual.tex
	hevea/bin/hevea -fix lem-manual.tex

# Using the stored Ott system definition seems to trigger the infamous
# Fatal error: exception New_term_parser.Reject_parse
# bug.
#lem-manual.tex: lem-manual.mng lem.ottsys lem.tex
#	rm -f lem-manual.tex
#	ott -readsys lem.ottsys -tex_filter lem-manual.mng lem-manual.tex 
#	chmod a-w lem-manual.tex

lem.ottsys: ../language/lem.ott
	ott -writesys lem.ottsys ../language/lem.ott

lem.tex: lem.ottsys
	ott -readsys lem.ottsys -o lem.tex -tex_wrap false

hevea/bin/hevea: hevea-1.10.tar.gz
	rm -rf hevea-1.10
	tar -xzf hevea-1.10.tar.gz
	make -C hevea-1.10
	make -C hevea-1.10 install
	rm -rf hevea-1.10/*

clean:
	rm -rf lem-manual.pdf lem-manual.ps lem-manual.dvi lem-manual.out lem-manual.aux lem-manual.log lem-manual.tex lem.ottsys lem.tex lem-manual.haux lem-manual.htoc lem-manual.html

cleanall: clean
	rm -rf hevea-1.10
	rm -rf hevea
