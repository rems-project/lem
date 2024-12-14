INSTALLDIR := $(shell ocamlfind printconf destdir)
LOCALINSTALDIR := local

all: extract_zarith extract_num
.PHONY: all
.DEFAULT_GOAL: all

install: install_zarith install_num install_lem
.PHONY: install

local-install:
	mkdir -p $(LOCALINSTALDIR)
	$(MAKE) INSTALLDIR=$(LOCALINSTALDIR) install
.PHONY: local-install

uninstall: uninstall_lem uninstall_zarith uninstall_num
.PHONY: uninstall

clean:
	ocamlbuild -build-dir _build_num -clean
	ocamlbuild -build-dir _build_zarith -clean
.PHONY: clean




extract_zarith extract_num: extract_%:
	@ocamlfind query $* > /dev/null || { echo "please install the missing $* package (or do 'make install_dependencies' from `pwd`)" && false; }
	ocamlbuild -build-dir _build_$* -X $(LOCALINSTALDIR) -X dependencies -I num_impl_$* -use-ocamlfind -pkg $* extract.cma extract.cmxa
.PHONY: extract_zarith extract_num

install_zarith install_num: install_%: extract_%
	-ocamlfind remove -destdir "$(INSTALLDIR)" lem_$*
	ocamlfind install -destdir "$(INSTALLDIR)" -patch-version "$(LEMVERSION)" lem_$* num_impl_$*/META _build_$*/extract.cma _build_$*/extract.cmxa _build_$*/extract.a `find _build_$* -name '*.cmi' -o -name '*.cmx' -o -name '*.mli'`
	touch $@
.PHONY: install_zarith install_num

uninstall_zarith uninstall_num: uninstall_%:
	-ocamlfind remove -destdir "$(INSTALLDIR)" lem_$*
.PHONY: uninstall_zarith uninstall_num


install_lem:
	-ocamlfind remove -destdir "$(INSTALLDIR)" lem
	ocamlfind install -destdir "$(INSTALLDIR)" -patch-version "$(LEMVERSION)" lem META
	touch $@
.PHONY: install_lem

uninstall_lem:
	-ocamlfind remove -destdir "$(INSTALLDIR)" lem
.PHONY: uninstall_lem




.PHONY: install_dependencies
install_dependencies:
	$(MAKE) -C dependencies install
