INSTALLDIR := $(shell ocamlfind printconf destdir)
LEMVERSION := $(shell git describe --dirty --always)

all: extract_zarith extract_num
.PHONY: all
.DEFAULT_GOAL: all

install: install_zarith install_num install_lem
.PHONY: install

uninstall: uninstall_lem uninstall_zarith uninstall_num
.PHONY: uninstall

clean:
	ocamlbuild -build-dir _build_num -clean
	ocamlbuild -build-dir _build_zarith -clean
.PHONY: clean




extract_zarith extract_num: extract_%:
	@ocamlfind query $* > /dev/null || { echo "please install the missing $* package (or do 'make install_dependencies' from `pwd`)" && false; }
	ocamlbuild -build-dir _build_$* -X dependencies -I num_impl_$* -use-ocamlfind -pkg $* extract.cma extract.cmxa
.PHONY: extract_zarith extract_num

install_zarith install_num: install_%: extract_%
	$(MAKE) $(INSTALLDIR)/lem_$*/META
.PHONY: install_zarith install_num

uninstall_zarith uninstall_num: uninstall_%:
	-ocamlfind remove lem_$*
.PHONY: uninstall_zarith uninstall_num

$(INSTALLDIR)/lem_zarith/META $(INSTALLDIR)/lem_num/META: $(INSTALLDIR)/lem_%/META: num_impl_%/META _build_%/extract.cma _build_%/extract.cmxa _build_%/extract.a
	-ocamlfind remove lem_$*
	ocamlfind install -patch-version "$(LEMVERSION)" lem_$* $^ `find _build_$* -name '*.cmi' -o -name '*.cmx' -o -name '*.mli'`
	touch $@




install_lem:
	$(MAKE) $(INSTALLDIR)/lem/META
.PHONY: install_lem

uninstall_lem:
	-ocamlfind remove lem
.PHONY: uninstall_lem


$(INSTALLDIR)/lem/META: META
	-ocamlfind remove lem
	ocamlfind install -patch-version "$(LEMVERSION)" lem $^
	touch $@




.PHONY: install_dependencies
install_dependencies:
	make -C dependencies install
