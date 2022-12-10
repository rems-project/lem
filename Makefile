# Attempt to ask git for a version (tag or hash) but fall back on LEMRELEASE.
# Note that opam builds from a tar ball so LEMRELEASE will be used in that case.
LEMRELEASE:=2022-12-10
LEMVERSION:=$(shell git describe --dirty --always 2>/dev/null || echo $(LEMRELEASE))

DDIR=lem-$(LEMVERSION)

# by default assume local install
INSTALL_DIR := $(realpath .)

#all: il.pdf build-main ilTheory.uo
all: bin/lem libs_phase_1

# we might want run the tests for all backends that are present

install:
	mkdir -p $(INSTALL_DIR)/bin
	rm -f $(INSTALL_DIR)/bin/lem
	cp src/main.native $(INSTALL_DIR)/bin/lem
	rm -rf $(INSTALL_DIR)/share/lem
	mkdir -p $(INSTALL_DIR)/share/lem/library
	cp library/*.lem $(INSTALL_DIR)/share/lem/library
	cp library/*_constants $(INSTALL_DIR)/share/lem/library
	$(MAKE) -C ocaml-lib install
	cp -R coq-lib $(INSTALL_DIR)/share/lem
	cp -R hol-lib $(INSTALL_DIR)/share/lem
#	cp -R html-lib $(INSTALL_DIR)/share/lem
	cp -R isabelle-lib $(INSTALL_DIR)/share/lem
#	cp -R tex-lib $(INSTALL_DIR)/share/lem

uninstall:
	rm -f $(INSTALL_DIR)/bin/lem
	rm -rf $(INSTALL_DIR)/share/lem
	$(MAKE) -C ocaml-lib uninstall

build-doc:
	$(MAKE) -C doc

do-tests:
	$(MAKE) -C tests

lem_dep.tex: lem_dep.ott
	ott -o lem_dep.tex -picky_multiple_parses true lem_dep.ott

lem_dep.pdf: lem_dep.tex
	pdflatex lem_dep.tex

# this runs Lem on the Lem library (library/*.lem), leaving the
# generated OCaml, Coq, HOL4, and Isabelle files to ocaml-libs,
# hol-libs, etc.
libs_phase_1: 
	$(MAKE) -C library
	$(MAKE) ocaml-libs


# this processes the Lem-generated library files for that target,
# together with any other hand-written files needed (eg the ocaml
# pset.ml), through the target.
libs_phase_2:
#	$(MAKE) ocaml-libs
	$(MAKE) tex-libs
	$(MAKE) hol-libs
	$(MAKE) coq-libs
	$(MAKE) isa-libs

hol-libs: 
#	$(MAKE) -C library hol-libs
	cd hol-lib; Holmake --qof -k
	$(MAKE) -C library hol-lib-tests

ocaml-libs:
#	$(MAKE) -C library ocaml-libs
	$(MAKE) -C ocaml-lib all
	$(MAKE) -C library ocaml-lib-tests

isa-libs: 
#	$(MAKE) -C library isa-libs
	isabelle build -d isabelle-lib -b LEM

coq-libs: 
#	$(MAKE) -C library coq-libs
	cd coq-lib; coqc -R . Lem coqharness.v
	cd coq-lib; coq_makefile -f coq_makefile.in > Makefile
	$(MAKE) -C coq-lib

tex-libs: 
#	$(MAKE) -C library tex-libs
	cd tex-lib; pdflatex lem-libs.tex
	cd tex-lib; pdflatex lem-libs.tex

# test-other: test-ppcmem test-cpp test-cppppc
# 
# test-ppc:
# 	# ppc model
# 	$(MAKE) -C ../../sem/WeakMemory/ppc-abstract-machine
# 	# pull ppc model into ppcmem directory
# 	# DON'T COMMIT
# 	$(MAKE) -C ../ppcmem/system model
# 
# test-axppc:
# 	# Sela model	
# 	$(MAKE) -C ../axppc
# 	# pull Sela model into ppcmem directory
# 	# DON'T COMMIT
# 	$(MAKE) -C ../ppcmem/system axmodel
# 
# test-arm:
# 	# ARM flowing model
# 	$(MAKE) -C ../arm/flowing-things
# 	# pull ARM model into ppcmem directory
# 	# DON'T COMMIT
# 	$(MAKE) -C ../ppcmem/system flowingmodel
# 
# test-ppcmem: test-ppc test-axppc test-arm
# 	# next 3 compile PPCMEM
# 	# Check makefile in ppcmem/system is set to "text"
# 	# DON'T commit
# 	$(MAKE) -C ../ppcmem/system clean
# 	$(MAKE) -C ../ppcmem/system depend_text
# 	$(MAKE) -C ../ppcmem/system text
# 
# test-cpp:
# 	# C++. Chat with Mark to fix
# 	$(MAKE) -C ../cpp/axiomatic/ntc deadlock
# 	# C++. Chat with Mark to fix HOL building and Mark/Susmit/Mike ML
# 	# building
# 	#$(MAKE) -C ../cpp/opsem
# 	#$(MAKE) -C ../cpp/axiomatic/ntc/proofs all
# 
# test-cppppc:
# 	$(MAKE) -C ../cppppc proof
# 	$(MAKE) -C ../cppppc/proof2 lem
# 
# 
# MACHINEFILES=\
# MachineDefUtils.lem \
# MachineDefFreshIds.lem \
# MachineDefValue.lem \
# MachineDefTypes.lem \
# MachineDefInstructionSemantics.lem \
# MachineDefStorageSubsystem.lem \
# MachineDefThreadSubsystem.lem \
# MachineDefSystem.lem
# 
# test-tex:  lem
# 	rm -rf tests/test-tex/*
# 	cp ../WeakMemory/ppc-abstract-machine/*.lem tests/test-tex
# 	cp tests/test-tex-inc-wrapper.tex tests/test-tex 
# 	chmod ugo-w tests/test-tex/*.lem
# 	cd tests/test-tex; ../../lem -hol -tex -ocaml -lib ../../library $(MACHINEFILES)
# 	cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex alldoc.tex; dvips alldoc
# 	cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex test-tex-inc-wrapper.tex; dvips test-tex-inc-wrapper
# 	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefUtils.tex; dvips MachineDefUtils
# 	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefFreshIds.tex; dvips MachineDefFreshIds
# 	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefValue.tex; dvips MachineDefValue
# 	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefTypes.tex; dvips MachineDefTypes
# 	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefInstructionSemantics.tex; dvips MachineDefInstructionSemantics
# 	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefStorageSubsystem.tex; dvips MachineDefStorageSubsystem
# 	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefThreadSubsystem.tex; dvips MachineDefThreadSubsystem
# 	#cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex MachineDefSystem.tex; dvips MachineDefSystem
# 
# test-texg:
# 	g tests/test-tex/alldoc
# 	#g tests/test-tex/MachineDefStorageSubsystem
# 
# test-texw:
# 	cd tests/test-tex; TEXINPUTS=../../tex-lib:$(TEXINPUTS) latex test-tex-inc-wrapper.tex; dvips test-tex-inc-wrapper
# 
# 
# test-texgw:
# 	g tests/test-tex/test-tex-inc-wrapper

debug: version share_directory
	rm -f library/lib_cache
	$(MAKE) -C src debug
	ln -sf src/main.d.byte lem


build-lem: version share_directory
	$(MAKE) -C src all
	ln -sf src/main.native lem

build-lem-profile: version share_directory
	$(MAKE) -C src profile
	ln -sf src/main.p.native lem-profile


lem: build-lem

bin/lem: lem
	mkdir -p bin
	cd bin && ln -sf ../src/main.native lem

OCAML-LIB-NON_LGPL =      \
ocaml-lib/Makefile	  \
ocaml-lib/big_int_impl.ml \
ocaml-lib/big_int_impl.mli \
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
	headache -h etc/header `ls src/*.ml`
	headache -h etc/header `ls src/*.mli`
	headache -h etc/header `ls src/*.mly`
	headache -h etc/header `ls src/*.mll`
	headache -c etc/head_config -h etc/header `ls language/*.lem`
	headache -c etc/head_config -h etc/header `ls tex-lib/*.sty`
	headache -c etc/head_config -h etc/header `ls coq-lib/*.v`
	headache -c etc/head_config -h etc/header `ls isabelle-lib/*.thy`
	headache -c etc/head_config -h etc/header `ls tex-lib/*.sty`
	headache -c etc/head_config -h etc/header $(OCAML-LIB-NONLGPL) 
	headache -c etc/head_config -h etc/header `ls library/coq/*.lem`
	headache -c etc/head_config -h etc/header `ls library/hol/*.lem`
	headache -c etc/head_config -h etc/header `ls library/isabelle/*.lem`
	headache -c etc/head_config -h etc/header `ls library/ocaml/*.lem`


#lem_unwrapped.tex: lem.ott
#	ott -tex_wrap false -o lem_unwrapped.tex lem.ott
#
#install_lem_unwrapped: lem_unwrapped.tex
#	cp lem_unwrapped.tex ../../ott/examples/ich/generated/lem_unwrapped.tex

#src/version.ml: 
version:
	echo "(* Generated file -- do not edit. *)" > src/version.ml
	echo 'let v="$(LEMVERSION)"' >> src/version.ml

share_directory:
	echo "(* Generated file -- do not edit. *)" > src/share_directory.ml
	echo let d=\"$(INSTALL_DIR)/share/lem\" >> src/share_directory.ml


distrib: src/ast.ml version
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
	headache -h header `ls $(DDIR)/src/*.ml`
	headache -h header `ls $(DDIR)/src/*.mli`
	headache -h header `ls $(DDIR)/src/*.mly`
	headache -h header `ls $(DDIR)/src/*.mll`
	headache -c head_config -h header `ls $(DDIR)/tex-lib/*.sty`
	headache -c head_config -h header `ls $(DDIR)/library/*.lem`
	headache -c head_config -h header `ls $(DDIR)/library/hol/*.lem`
	headache -c head_config -h header `ls $(DDIR)/library/isabelle/*.lem`
	headache -c head_config -h header `ls $(DDIR)/library/ocaml/*.lem`
	tar cf $(DDIR).tar $(DDIR)
	gzip $(DDIR).tar
	rm -rf $(DDIR)

clean:
	-$(MAKE) -C language clean
	-$(MAKE) -C src clean
	-$(MAKE) -C coq-lib clean
	-$(MAKE) -C ocaml-lib clean
	-$(MAKE) -C tex-lib clean
	-rm -f coq-lib/Makefile
	-rm -f coq-lib/coqharness.vo
	-rm -f coq-lib/coqharness.glob
	-rm -rf src/version.ml lem library/lib_cache src/share_directory.ml
	#-rm -rf lem_dep.tex lem_dep.pdf lem_dep.aux lem_dep.log

cleanall: clean
	-$(MAKE) -C doc clean
	-$(MAKE) -C slides clean
	-$(MAKE) -C manual cleanall
	-$(MAKE) -C ocaml-lib clean
	-$(MAKE) -C tests clean
	-rm -rf lem-$(LEMVERSION) lem-$(LEMVERSION).tar.gz
