LEMVERSION=0.3.1
DDIR=lem-$(LEMVERSION)

PATH := $(CURDIR)/$(FINDLIB)/bin:$(PATH)

#all: il.pdf build-main ilTheory.uo
all: build-lem
build-doc:
	make -C doc
do-tests:
	make -C tests

lem_dep.tex: lem_dep.ott
	ott -o lem_dep.tex -picky_multiple_parses true lem_dep.ott

lem_dep.pdf: lem_dep.tex
	pdflatex lem_dep.tex

test-other: test-ppcmem test-cpp test-cppppc

test-ppc:
	# ppc model
	make -C ../../sem/WeakMemory/ppc-abstract-machine 
	# pull ppc model into ppcmem directory
	# DON'T COMMIT
	make -C ../ppcmem/system model

test-axppc:
	# Sela model	
	make -C ../axppc
	# pull Sela model into ppcmem directory
	# DON'T COMMIT
	make -C ../ppcmem/system axmodel

test-arm:
	# ARM flowing model
	make -C ../arm/flowing-things
	# pull ARM model into ppcmem directory
	# DON'T COMMIT
	make -C ../ppcmem/system flowingmodel

test-ppcmem: test-ppc test-axppc test-arm
	# next 3 compile PPCMEM
	# Check makefile in ppcmem/system is set to "text"
	# DON'T commit
	make -C ../ppcmem/system clean
	make -C ../ppcmem/system depend_text
	make -C ../ppcmem/system text

test-cpp:
	# C++. Chat with Mark to fix
	make -C ../cpp/axiomatic/ntc deadlock
	# C++. Chat with Mark to fix HOL building and Mark/Susmit/Mike ML
	# building
	#make -C ../cpp/opsem
	#make -C ../cpp/axiomatic/ntc/proofs all

test-cppppc:
	make -C ../cppppc proof
	make -C ../cppppc/proof2 lem


MACHINEFILES=\
MachineDefUtils.lem \
MachineDefFreshIds.lem \
MachineDefValue.lem \
MachineDefTypes.lem \
MachineDefInstructionSemantics.lem \
MachineDefStorageSubsystem.lem \
MachineDefThreadSubsystem.lem \
MachineDefSystem.lem

test-tex:  lem
	rm -rf tests/test-tex/*
	cp ../WeakMemory/ppc-abstract-machine/*.lem tests/test-tex
	cp tests/test-tex-inc-wrapper.tex tests/test-tex 
	chmod ugo-w tests/test-tex/*.lem
	cd tests/test-tex; ../../lem -hol -tex -ocaml -lib ../../library $(MACHINEFILES)
	cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex alldoc.tex; dvips alldoc
	cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex test-tex-inc-wrapper.tex; dvips test-tex-inc-wrapper
	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefUtils.tex; dvips MachineDefUtils
	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefFreshIds.tex; dvips MachineDefFreshIds
	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefValue.tex; dvips MachineDefValue
	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefTypes.tex; dvips MachineDefTypes
	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefInstructionSemantics.tex; dvips MachineDefInstructionSemantics
	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefStorageSubsystem.tex; dvips MachineDefStorageSubsystem
	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefThreadSubsystem.tex; dvips MachineDefThreadSubsystem
	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefSystem.tex; dvips MachineDefSystem

test-texg:
	g tests/test-tex/alldoc
	#g tests/test-tex/MachineDefStorageSubsystem

test-texw:
	cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex test-tex-inc-wrapper.tex; dvips test-tex-inc-wrapper


test-texgw:
	g tests/test-tex/test-tex-inc-wrapper

debug: src/ast.ml src/version.ml
	rm -f library/lib_cache
	make -C src debug
	ln -sf src/main.d.byte lem


build-lem: src/ast.ml src/version.ml
	rm -f library/lib_cache
	make -C ocaml-lib all
	make -C src all
	ln -sf src/main.native lem

lem-doc: build-lem
	make -C src doc
	ln -sf src/html-doc .
	make -C src doc-pdf
	ln -sf src/tex-doc/lem-doc.pdf .
	make -C src doc-dot
	ln -sf src/dep.pdf lem-doc-dep.pdf

lem: build-lem

headache: headache-1.03.tar.gz
	tar xzf headache-1.03.tar.gz
	cd headache-1.03; ./configure --bindir $(CURDIR)/headache
	make -C headache-1.03
	make -C headache-1.03 install
	rm -rf headache-1.03

OCAML-LIB-NON_LGPL =      \
ocaml-lib/Makefile	  \
ocaml-lib/nat_big_num.ml  \
ocaml-lib/nat_big_num.mli \
ocaml-lib/nat_num.ml	  \
ocaml-lib/nat_num.mli	  \
ocaml-lib/vector.ml       \
ocaml-lib/vector.mli
#  not
# pmap.ml
# pmap.mli
# pset.ml
# pset.mli

apply_header:
	./headache -h etc/header `ls src/*.ml`
	./headache -h etc/header `ls src/*.mli`
	./headache -h etc/header `ls src/*.mly`
	./headache -h etc/header `ls src/*.mll`
	./headache -c etc/head_config -h etc/header `ls language/*.lem`
	./headache -c etc/head_config -h etc/header `ls tex-lib/*.sty`
	./headache -c etc/head_config -h etc/header `ls coq-lib/*.v`
	./headache -c etc/head_config -h etc/header `ls isabelle-lib/*.thy`
	./headache -c etc/head_config -h etc/header `ls tex-lib/*.sty`
	./headache -c etc/head_config -h etc/header $(OCAML-LIB-NONLGPL) 
	./headache -c etc/head_config -h etc/header `ls library/coq/*.lem`
	./headache -c etc/head_config -h etc/header `ls library/hol/*.lem`
	./headache -c etc/head_config -h etc/header `ls library/isabelle/*.lem`
	./headache -c etc/head_config -h etc/header `ls library/ocaml/*.lem`


#lem_unwrapped.tex: lem.ott
#	ott -tex_wrap false -o lem_unwrapped.tex lem.ott
#
#install_lem_unwrapped: lem_unwrapped.tex
#	cp lem_unwrapped.tex ../../ott/examples/ich/generated/lem_unwrapped.tex

src/version.ml: Makefile
	echo 'let v="$(LEMVERSION)"' > src/version.ml
	chmod a-x src/version.ml

distrib: src/ast.ml src/version.ml headache
	rm -rf $(DDIR)
	rm -rf $(DDIR).tar.gz
	mkdir $(DDIR)
	mkdir $(DDIR)/src
	mkdir $(DDIR)/src/ulib
	cp src/*.ml $(DDIR)/src/
	chmod a+w $(DDIR)/src/ast.ml
	chmod a+w $(DDIR)/src/version.ml
	cp src/*.mli $(DDIR)/src/
	cp src/*.mll $(DDIR)/src/
	cp src/*.mly $(DDIR)/src/
	cp src/_tags $(DDIR)/src/
	cp src/ulib/*.ml $(DDIR)/src/ulib/
	cp src/ulib/*.mli $(DDIR)/src/ulib/
	mkdir $(DDIR)/library
	mkdir $(DDIR)/library/hol
	mkdir $(DDIR)/library/isabelle
	mkdir $(DDIR)/library/ocaml
	cp library/*.lem $(DDIR)/library/
	cp library/isabelle/constants $(DDIR)/library/isabelle/
	cp library/isabelle/*.lem $(DDIR)/library/isabelle/
	cp library/hol/constants $(DDIR)/library/hol/
	cp library/hol/*.lem $(DDIR)/library/hol/
	cp library/ocaml/*.lem $(DDIR)/library/ocaml/
	mkdir $(DDIR)/ocaml-lib
	cp ocaml-lib/*.ml $(DDIR)/ocaml-lib	
	cp ocaml-lib/*.mli $(DDIR)/ocaml-lib	
	cp ocaml-lib/*.mllib $(DDIR)/ocaml-lib	
	cp ocaml-lib/Makefile $(DDIR)/ocaml-lib	
	mkdir $(DDIR)/tex-lib
	cp tex-lib/lem.sty $(DDIR)/tex-lib
	cp Makefile-distrib $(DDIR)/Makefile
	cp src/Makefile-distrib $(DDIR)/src/Makefile
	cp README $(DDIR)
	cp LICENSE $(DDIR)
	./headache -h header `ls $(DDIR)/src/*.ml`
	./headache -h header `ls $(DDIR)/src/*.mli`
	./headache -h header `ls $(DDIR)/src/*.mly`
	./headache -h header `ls $(DDIR)/src/*.mll`
	./headache -c head_config -h header `ls $(DDIR)/tex-lib/*.sty`
	./headache -c head_config -h header `ls $(DDIR)/library/*.lem`
	./headache -c head_config -h header `ls $(DDIR)/library/hol/*.lem`
	./headache -c head_config -h header `ls $(DDIR)/library/isabelle/*.lem`
	./headache -c head_config -h header `ls $(DDIR)/library/ocaml/*.lem`
	tar cf $(DDIR).tar $(DDIR)
	gzip $(DDIR).tar
	rm -rf $(DDIR)

clean:
	-make -C language clean
	-make -C src clean
	-rm -rf src/version.ml lem library/lib_cache
	#-rm -rf lem_dep.tex lem_dep.pdf lem_dep.aux lem_dep.log

cleanall: clean
	-make -C doc clean
	-make -C slides clean
	-make -C manual cleanall
	-make -C ocaml-lib clean
	-make -C tests clean
	-rm -rf headache
	-rm -rf lem-$(LEMVERSION) lem-$(LEMVERSION).tar.gz
