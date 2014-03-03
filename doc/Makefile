

##  build all documentation and create links from this directory to it

all: 
# manual
	make -C manual
	ln -sf manual/lem-manual.html .
	ln -sf manual/lem-manual.pdf .
# lem Ott grammar
	make -C ../language 
	ln -sf ../language/lem.pdf .
# library documentation
	make -C .. tex-libs
	ln -sf ../tex-lib/lem-libs.pdf .
	../lem -print_env ../library/pervasives.lem > lem-libs-pervasives.txt  
	../lem -print_env ../library/pervasives_extra.lem > lem-libs-pervasives-extra.txt
# source documentation
	make -C ../src .
	ln -sf ../src/html-doc .
	make -C ../src doc-pdf
	ln -sf ../src/tex-doc/lem-doc.pdf .
	make -C ../src doc-dot
	ln -sf ../src/dep.pdf  .


# pull lem-draft.pdf
pull-lem-draft:
	cp ~/rsem/lem/doc/pldi2014-submission/lem-icfp-2014.pdf  lem-draft.pdf 



## copy built documentation 

TARGET=built-doc
snapshot:
	cp -rL lem-manual.html $(TARGET)
	cp lem-manual.pdf $(TARGET)
	cp lem.pdf $(TARGET)
	cp lem-libs.pdf $(TARGET)
	cp lem-libs-pervasives.txt $(TARGET)
	cp lem-libs-pervasives-extra.txt $(TARGET)
	cp lem-doc.pdf $(TARGET)
	cp dep.pdf $(TARGET)
	cp lem-draft.pdf $(TARGET)

# not building?
#	cp -rL html-doc $(TARGET)

INSTALL_TARGET=~/public_html/lem
install:
	cp index.html $(INSTALL_TARGET)
	cp style.css $(INSTALL_TARGET)
	cp -r built-doc $(INSTALL_TARGET)

clean:
	rm -rf dep.pdf html-doc doc-dep.pdf doc.pdf lem.pdf lem-libs.pdf lem-manual.html lem-manual.pdf lem-doc.pdf
	rm -rf lem-libs-pervasives-extra.txt
	rm -rf lem-libs-pervasives.txt

cleansnapshot:
	rm -rf built-doc/*
