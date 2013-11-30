all: Out10.pdf

Out10.pdf: out10.lem
	lem -wl_unused_vars ign -tex out10.lem && \
   TEXINPUTS=~/bitbucket/lem/tex-lib/:.:  pdflatex Out10.tex

clean:
	rm -rf *~
	rm -rf    \
Out10.aux         \
Out10-inc.tex	  \
Out10.log	  \
Out10.pdf	  \
Out10.tex         \
Out10-use_inc.tex
